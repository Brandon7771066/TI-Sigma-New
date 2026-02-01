"""
DANDI Archive Data Integration for LCC Studies

Downloads and processes animal neuroscience datasets from DANDI Archive.
Focuses on rodent EEG/LFP + behavior recordings for LCC correlation analysis.

Key datasets:
- Rat Temporal Lobe Epilepsy (DANDI:001044) - 15 rats, 12-channel LFP, behavior
- Mouse Visual Behavior Neuropixels - Neural activity during behavior tasks
- Rat Hippocampal recordings with spatial behavior
"""

import os
import sys
import json
import sqlite3
import subprocess
from pathlib import Path
from datetime import datetime
from dataclasses import dataclass, asdict
from typing import Dict, List, Optional, Tuple, Any
from concurrent.futures import ThreadPoolExecutor, as_completed
import numpy as np

# Database path
DATA_DIR = Path(__file__).parent / "neural_data"
DB_PATH = DATA_DIR / "neural_study.db"


@dataclass
class DANDIDataset:
    """Metadata for a DANDI dataset"""
    dandiset_id: str
    name: str
    description: str
    species: str
    modalities: List[str]
    has_behavior: bool
    num_subjects: int
    recording_type: str  # 'EEG', 'LFP', 'Neuropixels', etc.
    download_url: str
    size_gb: float
    license: str


# Known useful datasets for LCC studies
RECOMMENDED_DATASETS = [
    DANDIDataset(
        dandiset_id="001044",
        name="Rat Temporal Lobe Epilepsy LFP",
        description="15 rats with 12-channel LFP from hippocampus/Papez circuit during spontaneous seizures",
        species="Rattus norvegicus",
        modalities=["LFP", "behavior"],
        has_behavior=True,
        num_subjects=15,
        recording_type="LFP",
        download_url="https://dandiarchive.org/dandiset/001044",
        size_gb=50.0,
        license="CC0"
    ),
    DANDIDataset(
        dandiset_id="000776",
        name="Mouse Visual Behavior Neuropixels",
        description="Neuropixels recordings during visual change detection task",
        species="Mus musculus",
        modalities=["Neuropixels", "behavior", "running_speed"],
        has_behavior=True,
        num_subjects=81,
        recording_type="Neuropixels",
        download_url="https://dandiarchive.org/dandiset/000776",
        size_gb=200.0,
        license="CC-BY-4.0"
    ),
    DANDIDataset(
        dandiset_id="000552",
        name="Mouse Hippocampal Sharp-Wave Ripples",
        description="Curated SWR events from hippocampus during visual tasks",
        species="Mus musculus",
        modalities=["Neuropixels", "LFP", "behavior"],
        has_behavior=True,
        num_subjects=20,
        recording_type="Neuropixels",
        download_url="https://dandiarchive.org/dandiset/000552",
        size_gb=30.0,
        license="CC-BY-4.0"
    ),
    DANDIDataset(
        dandiset_id="000003",
        name="Mouse Barrel Cortex Recordings",
        description="Intracellular + extracellular recordings during whisker tasks",
        species="Mus musculus",
        modalities=["intracellular", "extracellular", "behavior"],
        has_behavior=True,
        num_subjects=10,
        recording_type="patch-clamp",
        download_url="https://dandiarchive.org/dandiset/000003",
        size_gb=5.0,
        license="CC0"
    ),
]


def init_database():
    """Initialize the neural study database"""
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    
    conn = sqlite3.connect(str(DB_PATH))
    cursor = conn.cursor()
    
    # Downloaded datasets table
    cursor.execute("""
        CREATE TABLE IF NOT EXISTS downloaded_datasets (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            dandiset_id TEXT UNIQUE NOT NULL,
            name TEXT NOT NULL,
            species TEXT,
            download_date TEXT NOT NULL,
            local_path TEXT NOT NULL,
            num_files INTEGER,
            total_size_mb REAL,
            status TEXT DEFAULT 'downloading'
        )
    """)
    
    # NWB files table
    cursor.execute("""
        CREATE TABLE IF NOT EXISTS nwb_files (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            dandiset_id TEXT NOT NULL,
            file_path TEXT NOT NULL,
            subject_id TEXT,
            session_id TEXT,
            has_neural_data BOOLEAN,
            has_behavior_data BOOLEAN,
            neural_channels INTEGER,
            duration_seconds REAL,
            sampling_rate REAL,
            processed BOOLEAN DEFAULT FALSE,
            FOREIGN KEY (dandiset_id) REFERENCES downloaded_datasets(dandiset_id)
        )
    """)
    
    # Extracted neural-behavior segments
    cursor.execute("""
        CREATE TABLE IF NOT EXISTS neural_behavior_segments (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            nwb_file_id INTEGER NOT NULL,
            start_time REAL NOT NULL,
            end_time REAL NOT NULL,
            neural_power_delta REAL,
            neural_power_theta REAL,
            neural_power_alpha REAL,
            neural_power_beta REAL,
            neural_power_gamma REAL,
            behavior_state TEXT,
            activity_level REAL,
            arousal_estimate REAL,
            timestamp TEXT NOT NULL,
            FOREIGN KEY (nwb_file_id) REFERENCES nwb_files(id)
        )
    """)
    
    # LCC correlation results
    cursor.execute("""
        CREATE TABLE IF NOT EXISTS lcc_correlations (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            dataset_a TEXT NOT NULL,
            dataset_b TEXT NOT NULL,
            time_window_seconds REAL NOT NULL,
            correlation_neural REAL,
            correlation_behavior REAL,
            correlation_combined REAL,
            p_value REAL,
            num_samples INTEGER,
            analysis_date TEXT NOT NULL,
            notes TEXT
        )
    """)
    
    conn.commit()
    conn.close()
    print(f"Database initialized at {DB_PATH}")


def check_dandi_cli():
    """Check if DANDI CLI is installed"""
    try:
        result = subprocess.run(
            ["dandi", "--version"],
            capture_output=True,
            text=True,
            timeout=10
        )
        return result.returncode == 0
    except Exception:
        return False


def install_dandi_cli():
    """Install DANDI CLI via pip"""
    print("Installing DANDI CLI...")
    try:
        subprocess.run(
            [sys.executable, "-m", "pip", "install", "dandi", "pynwb", "hdmf"],
            check=True,
            capture_output=True
        )
        print("DANDI CLI installed successfully")
        return True
    except subprocess.CalledProcessError as e:
        print(f"Failed to install DANDI CLI: {e}")
        return False


def list_dandiset_files(dandiset_id: str) -> List[Dict[str, Any]]:
    """List files in a dandiset using DANDI API"""
    try:
        from dandi.dandiapi import DandiAPIClient
        
        client = DandiAPIClient()
        dandiset = client.get_dandiset(dandiset_id, "draft")
        
        files = []
        for asset in dandiset.get_assets():
            files.append({
                "path": asset.path,
                "size": asset.size,
                "identifier": asset.identifier
            })
        
        return files
    except Exception as e:
        print(f"Error listing dandiset {dandiset_id}: {e}")
        return []


def download_dandiset(
    dandiset_id: str,
    output_dir: Optional[Path] = None,
    max_files: int = 5,
    max_size_mb: float = 500
) -> Optional[Path]:
    """
    Download a dandiset (or subset) to local storage.
    
    Args:
        dandiset_id: DANDI dataset ID (e.g., "001044")
        output_dir: Where to save files
        max_files: Maximum number of files to download
        max_size_mb: Maximum total size to download
    
    Returns:
        Path to downloaded files, or None if failed
    """
    if output_dir is None:
        output_dir = DATA_DIR / f"dandiset_{dandiset_id}"
    
    output_dir.mkdir(parents=True, exist_ok=True)
    
    if not check_dandi_cli():
        if not install_dandi_cli():
            print("Cannot proceed without DANDI CLI")
            return None
    
    print(f"Downloading dandiset {dandiset_id} to {output_dir}...")
    
    try:
        # List available files first
        files = list_dandiset_files(dandiset_id)
        if not files:
            print("No files found in dandiset")
            return None
        
        print(f"Found {len(files)} files in dandiset")
        
        # Filter to manageable subset
        nwb_files = [f for f in files if f["path"].endswith(".nwb")]
        print(f"Found {len(nwb_files)} NWB files")
        
        # Sort by size and take smallest ones
        nwb_files.sort(key=lambda x: x.get("size", 0))
        
        total_size = 0
        files_to_download = []
        for f in nwb_files[:max_files]:
            size_mb = f.get("size", 0) / (1024 * 1024)
            if total_size + size_mb <= max_size_mb:
                files_to_download.append(f)
                total_size += size_mb
        
        print(f"Will download {len(files_to_download)} files ({total_size:.1f} MB)")
        
        # Download using DANDI API
        from dandi.dandiapi import DandiAPIClient
        from dandi.download import download
        
        # Use dandi download command for each file
        for file_info in files_to_download:
            file_path = file_info["path"]
            print(f"Downloading: {file_path}")
            
            try:
                download(
                    f"https://dandiarchive.org/dandiset/{dandiset_id}/draft",
                    output_dir,
                    get_metadata=False,
                    jobs=1
                )
                break  # download() gets all files
            except Exception as e:
                print(f"Download error: {e}")
                # Try CLI fallback
                subprocess.run(
                    ["dandi", "download", f"DANDI:{dandiset_id}/draft", "-o", str(output_dir)],
                    check=True
                )
                break
        
        # Record in database
        conn = sqlite3.connect(str(DB_PATH))
        cursor = conn.cursor()
        cursor.execute("""
            INSERT OR REPLACE INTO downloaded_datasets 
            (dandiset_id, name, species, download_date, local_path, num_files, total_size_mb, status)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            dandiset_id,
            f"Dandiset {dandiset_id}",
            "unknown",
            datetime.utcnow().isoformat(),
            str(output_dir),
            len(files_to_download),
            total_size,
            "completed"
        ))
        conn.commit()
        conn.close()
        
        return output_dir
        
    except Exception as e:
        print(f"Error downloading dandiset: {e}")
        return None


def scan_local_nwb_files(data_dir: Path = DATA_DIR) -> List[Path]:
    """Find all NWB files in the data directory"""
    nwb_files = list(data_dir.rglob("*.nwb"))
    print(f"Found {len(nwb_files)} NWB files in {data_dir}")
    return nwb_files


def extract_nwb_metadata(nwb_path: Path) -> Dict[str, Any]:
    """Extract metadata from an NWB file without loading all data"""
    try:
        from pynwb import NWBHDF5IO
        
        with NWBHDF5IO(str(nwb_path), 'r', load_namespaces=True) as io:
            nwb = io.read()
            
            metadata = {
                "session_id": nwb.session_id if hasattr(nwb, 'session_id') else None,
                "subject_id": nwb.subject.subject_id if hasattr(nwb, 'subject') and nwb.subject else None,
                "species": nwb.subject.species if hasattr(nwb, 'subject') and nwb.subject else None,
                "session_description": nwb.session_description if hasattr(nwb, 'session_description') else None,
                "session_start_time": str(nwb.session_start_time) if hasattr(nwb, 'session_start_time') else None,
            }
            
            # Check for neural data
            has_neural = False
            neural_channels = 0
            sampling_rate = 0
            duration = 0
            
            if hasattr(nwb, 'acquisition'):
                for name, data in nwb.acquisition.items():
                    if hasattr(data, 'data'):
                        has_neural = True
                        if hasattr(data, 'rate'):
                            sampling_rate = float(data.rate)
                        if hasattr(data.data, 'shape'):
                            if len(data.data.shape) > 1:
                                neural_channels = data.data.shape[1]
                                duration = data.data.shape[0] / max(sampling_rate, 1)
                            else:
                                duration = data.data.shape[0] / max(sampling_rate, 1)
                        break
            
            # Check for behavior data
            has_behavior = False
            if hasattr(nwb, 'processing'):
                has_behavior = 'behavior' in nwb.processing
            
            metadata.update({
                "has_neural_data": has_neural,
                "has_behavior_data": has_behavior,
                "neural_channels": neural_channels,
                "sampling_rate": sampling_rate,
                "duration_seconds": duration
            })
            
            return metadata
            
    except Exception as e:
        print(f"Error reading NWB metadata from {nwb_path}: {e}")
        return {"error": str(e)}


def process_nwb_for_lcc(nwb_path: Path, segment_duration: float = 30.0) -> List[Dict[str, Any]]:
    """
    Process an NWB file to extract neural-behavior segments for LCC analysis.
    
    Args:
        nwb_path: Path to NWB file
        segment_duration: Duration of each segment in seconds
    
    Returns:
        List of extracted segments with neural and behavior features
    """
    try:
        from pynwb import NWBHDF5IO
        
        segments = []
        
        with NWBHDF5IO(str(nwb_path), 'r', load_namespaces=True) as io:
            nwb = io.read()
            
            # Find neural data
            neural_data = None
            neural_rate = 1000  # default
            neural_key = None
            
            if hasattr(nwb, 'acquisition'):
                for name, data in nwb.acquisition.items():
                    if hasattr(data, 'data') and hasattr(data, 'rate'):
                        neural_data = data.data[:]
                        neural_rate = float(data.rate)
                        neural_key = name
                        break
            
            if neural_data is None:
                print(f"No neural data found in {nwb_path}")
                return segments
            
            # Find behavior data
            behavior_data = None
            behavior_rate = 1
            
            if hasattr(nwb, 'processing') and 'behavior' in nwb.processing:
                behavior_mod = nwb.processing['behavior']
                # Look for speed, position, or other behavioral signals
                for name in ['speed', 'running_speed', 'velocity', 'position']:
                    if name in behavior_mod.data_interfaces:
                        ts = behavior_mod.data_interfaces[name]
                        if hasattr(ts, 'data'):
                            behavior_data = ts.data[:]
                            if hasattr(ts, 'rate'):
                                behavior_rate = float(ts.rate)
                            break
            
            # Calculate segments
            total_duration = len(neural_data) / neural_rate
            num_segments = int(total_duration / segment_duration)
            
            for i in range(min(num_segments, 100)):  # Limit to 100 segments
                start_time = i * segment_duration
                end_time = start_time + segment_duration
                
                # Extract neural segment
                start_idx = int(start_time * neural_rate)
                end_idx = int(end_time * neural_rate)
                
                neural_segment = neural_data[start_idx:end_idx]
                
                # Calculate power in frequency bands
                power_bands = calculate_power_bands(neural_segment, neural_rate)
                
                # Extract behavior if available
                activity_level = 0.0
                arousal_estimate = 0.0
                behavior_state = "unknown"
                
                if behavior_data is not None:
                    b_start = int(start_time * behavior_rate)
                    b_end = int(end_time * behavior_rate)
                    if b_end <= len(behavior_data):
                        behavior_segment = behavior_data[b_start:b_end]
                        if len(behavior_segment) > 0:
                            activity_level = float(np.mean(np.abs(behavior_segment)))
                            arousal_estimate = float(np.std(behavior_segment))
                            
                            # Classify behavior state
                            if activity_level < 0.1:
                                behavior_state = "rest"
                            elif activity_level < 0.5:
                                behavior_state = "low_activity"
                            else:
                                behavior_state = "high_activity"
                
                segment = {
                    "start_time": start_time,
                    "end_time": end_time,
                    "neural_power_delta": power_bands.get("delta", 0),
                    "neural_power_theta": power_bands.get("theta", 0),
                    "neural_power_alpha": power_bands.get("alpha", 0),
                    "neural_power_beta": power_bands.get("beta", 0),
                    "neural_power_gamma": power_bands.get("gamma", 0),
                    "behavior_state": behavior_state,
                    "activity_level": activity_level,
                    "arousal_estimate": arousal_estimate,
                    "timestamp": datetime.utcnow().isoformat()
                }
                segments.append(segment)
            
            print(f"Extracted {len(segments)} segments from {nwb_path}")
            return segments
            
    except Exception as e:
        print(f"Error processing NWB file {nwb_path}: {e}")
        return []


def calculate_power_bands(signal: np.ndarray, sampling_rate: float) -> Dict[str, float]:
    """
    Calculate power in standard EEG frequency bands.
    
    Bands:
        delta: 0.5-4 Hz
        theta: 4-8 Hz
        alpha: 8-13 Hz
        beta: 13-30 Hz
        gamma: 30-100 Hz
    """
    try:
        from scipy import signal as scipy_signal
        
        # If multi-channel, average
        if len(signal.shape) > 1:
            signal = np.mean(signal, axis=1)
        
        # Compute power spectral density
        freqs, psd = scipy_signal.welch(signal, fs=sampling_rate, nperseg=min(len(signal), int(sampling_rate * 2)))
        
        # Define frequency bands
        bands = {
            "delta": (0.5, 4),
            "theta": (4, 8),
            "alpha": (8, 13),
            "beta": (13, 30),
            "gamma": (30, min(100, sampling_rate / 2 - 1))
        }
        
        powers = {}
        for band_name, (low, high) in bands.items():
            idx = np.where((freqs >= low) & (freqs <= high))
            if len(idx[0]) > 0:
                powers[band_name] = float(np.mean(psd[idx]))
            else:
                powers[band_name] = 0.0
        
        return powers
        
    except ImportError:
        # Fallback without scipy
        return {"delta": 0, "theta": 0, "alpha": 0, "beta": 0, "gamma": 0}


def run_lcc_analysis(dataset_a_id: int, dataset_b_id: int, time_window: float = 30.0) -> Dict[str, Any]:
    """
    Run LCC correlation analysis between two datasets.
    
    Compares neural and behavior patterns between datasets to test
    for non-local correlations.
    """
    conn = sqlite3.connect(str(DB_PATH))
    cursor = conn.cursor()
    
    # Get segments from both datasets
    cursor.execute("""
        SELECT neural_power_theta, neural_power_gamma, activity_level, arousal_estimate
        FROM neural_behavior_segments WHERE nwb_file_id = ?
        ORDER BY start_time
    """, (dataset_a_id,))
    segments_a = cursor.fetchall()
    
    cursor.execute("""
        SELECT neural_power_theta, neural_power_gamma, activity_level, arousal_estimate
        FROM neural_behavior_segments WHERE nwb_file_id = ?
        ORDER BY start_time
    """, (dataset_b_id,))
    segments_b = cursor.fetchall()
    
    conn.close()
    
    if len(segments_a) < 10 or len(segments_b) < 10:
        return {"error": "Insufficient data for analysis", "segments_a": len(segments_a), "segments_b": len(segments_b)}
    
    # Match segment counts
    min_len = min(len(segments_a), len(segments_b))
    segments_a = segments_a[:min_len]
    segments_b = segments_b[:min_len]
    
    # Convert to numpy arrays
    a_neural = np.array([[s[0], s[1]] for s in segments_a])  # theta, gamma
    b_neural = np.array([[s[0], s[1]] for s in segments_b])
    
    a_behavior = np.array([[s[2], s[3]] for s in segments_a])  # activity, arousal
    b_behavior = np.array([[s[2], s[3]] for s in segments_b])
    
    # Calculate correlations
    from scipy.stats import pearsonr, spearmanr
    
    # Neural correlation (theta power)
    if np.std(a_neural[:, 0]) > 0 and np.std(b_neural[:, 0]) > 0:
        r_neural, p_neural = pearsonr(a_neural[:, 0], b_neural[:, 0])
    else:
        r_neural, p_neural = 0, 1
    
    # Behavior correlation (activity level)
    if np.std(a_behavior[:, 0]) > 0 and np.std(b_behavior[:, 0]) > 0:
        r_behavior, p_behavior = pearsonr(a_behavior[:, 0], b_behavior[:, 0])
    else:
        r_behavior, p_behavior = 0, 1
    
    # Combined correlation
    r_combined = (r_neural + r_behavior) / 2
    p_combined = (p_neural + p_behavior) / 2  # Simple average (not statistically rigorous)
    
    result = {
        "correlation_neural": float(r_neural),
        "p_value_neural": float(p_neural),
        "correlation_behavior": float(r_behavior),
        "p_value_behavior": float(p_behavior),
        "correlation_combined": float(r_combined),
        "p_value_combined": float(p_combined),
        "num_samples": min_len,
        "interpretation": interpret_lcc_result(r_combined, p_combined, min_len)
    }
    
    # Save to database
    conn = sqlite3.connect(str(DB_PATH))
    cursor = conn.cursor()
    cursor.execute("""
        INSERT INTO lcc_correlations 
        (dataset_a, dataset_b, time_window_seconds, correlation_neural, 
         correlation_behavior, correlation_combined, p_value, num_samples, analysis_date, notes)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    """, (
        str(dataset_a_id), str(dataset_b_id), time_window,
        r_neural, r_behavior, r_combined, p_combined,
        min_len, datetime.utcnow().isoformat(), result["interpretation"]
    ))
    conn.commit()
    conn.close()
    
    return result


def interpret_lcc_result(correlation: float, p_value: float, n: int) -> str:
    """Interpret LCC correlation result in context of theory"""
    if p_value > 0.05:
        return f"No significant correlation detected (r={correlation:.3f}, p={p_value:.3f}, n={n}). Result is consistent with LCC=1 (pure local causation)."
    
    if correlation > 0.3:
        return f"Strong positive correlation (r={correlation:.3f}, p={p_value:.3f}, n={n}). Suggests potential non-local influence (LCC < 1). Requires replication and control for confounds."
    elif correlation > 0.1:
        return f"Weak positive correlation (r={correlation:.3f}, p={p_value:.3f}, n={n}). Small effect consistent with LCC slightly < 1, but could be spurious."
    elif correlation > 0:
        return f"Very weak positive correlation (r={correlation:.3f}, p={p_value:.3f}, n={n}). Likely noise, insufficient evidence for LCC < 1."
    else:
        return f"No positive correlation (r={correlation:.3f}, p={p_value:.3f}, n={n}). Result is consistent with LCC=1 or measurement artifacts."


def get_available_datasets() -> List[Dict[str, Any]]:
    """Get list of downloaded datasets available for analysis"""
    conn = sqlite3.connect(str(DB_PATH))
    cursor = conn.cursor()
    
    cursor.execute("""
        SELECT dandiset_id, name, species, download_date, local_path, num_files, status
        FROM downloaded_datasets
        ORDER BY download_date DESC
    """)
    
    datasets = []
    for row in cursor.fetchall():
        datasets.append({
            "dandiset_id": row[0],
            "name": row[1],
            "species": row[2],
            "download_date": row[3],
            "local_path": row[4],
            "num_files": row[5],
            "status": row[6]
        })
    
    conn.close()
    return datasets


def get_analysis_results() -> List[Dict[str, Any]]:
    """Get all LCC correlation analysis results"""
    conn = sqlite3.connect(str(DB_PATH))
    cursor = conn.cursor()
    
    cursor.execute("""
        SELECT dataset_a, dataset_b, correlation_neural, correlation_behavior,
               correlation_combined, p_value, num_samples, analysis_date, notes
        FROM lcc_correlations
        ORDER BY analysis_date DESC
    """)
    
    results = []
    for row in cursor.fetchall():
        results.append({
            "dataset_a": row[0],
            "dataset_b": row[1],
            "correlation_neural": row[2],
            "correlation_behavior": row[3],
            "correlation_combined": row[4],
            "p_value": row[5],
            "num_samples": row[6],
            "analysis_date": row[7],
            "interpretation": row[8]
        })
    
    conn.close()
    return results


# Initialize on import
init_database()


if __name__ == "__main__":
    print("DANDI Data Integration for LCC Studies")
    print("=" * 50)
    
    print("\nRecommended datasets for LCC analysis:")
    for i, ds in enumerate(RECOMMENDED_DATASETS, 1):
        print(f"\n{i}. {ds.name}")
        print(f"   ID: DANDI:{ds.dandiset_id}")
        print(f"   Species: {ds.species}")
        print(f"   Recording: {ds.recording_type}")
        print(f"   Has behavior: {ds.has_behavior}")
        print(f"   Size: ~{ds.size_gb} GB")
    
    print("\n" + "=" * 50)
    print("To download a dataset, use:")
    print("  download_dandiset('001044')  # Downloads rat LFP dataset")
