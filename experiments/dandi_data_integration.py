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
    """List files in a dandiset using DANDI REST API (no SDK required)"""
    import requests
    
    try:
        # Use DANDI Archive REST API directly
        api_url = f"https://api.dandiarchive.org/api/dandisets/{dandiset_id}/versions/draft/assets/"
        
        files = []
        page_url = api_url
        
        while page_url:
            response = requests.get(page_url, timeout=30)
            response.raise_for_status()
            data = response.json()
            
            for asset in data.get("results", []):
                files.append({
                    "path": asset.get("path", "unknown"),
                    "size": asset.get("size", 0),
                    "size_mb": asset.get("size", 0) / (1024 * 1024),
                    "identifier": asset.get("asset_id", ""),
                    "blob": asset.get("blob", ""),
                    "created": asset.get("created", ""),
                    "content_url": asset.get("contentUrl", "")
                })
            
            # Handle pagination
            page_url = data.get("next")
            
            # Limit to first 100 files to avoid long queries
            if len(files) >= 100:
                break
        
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
    Download a dandiset (or subset) to local storage using direct HTTP.
    No SDK required - uses DANDI REST API directly.
    
    Args:
        dandiset_id: DANDI dataset ID (e.g., "001044")
        output_dir: Where to save files
        max_files: Maximum number of files to download
        max_size_mb: Maximum total size to download
    
    Returns:
        Path to downloaded files, or None if failed
    """
    import requests
    
    if output_dir is None:
        output_dir = DATA_DIR / f"dandiset_{dandiset_id}"
    
    output_dir.mkdir(parents=True, exist_ok=True)
    
    print(f"Downloading dandiset {dandiset_id} to {output_dir}...")
    
    try:
        # List available files first
        files = list_dandiset_files(dandiset_id)
        if not files:
            print("No files found in dandiset")
            return None
        
        print(f"Found {len(files)} files in dandiset")
        
        # Filter to NWB files only
        nwb_files = [f for f in files if f["path"].endswith(".nwb")]
        print(f"Found {len(nwb_files)} NWB files")
        
        if not nwb_files:
            print("No NWB files found - downloading first available file")
            nwb_files = files[:1]
        
        # Sort by size and take smallest ones
        nwb_files.sort(key=lambda x: x.get("size", 0))
        
        total_size = 0
        files_to_download = []
        for f in nwb_files[:max_files]:
            size_mb = f.get("size_mb", 0)
            if total_size + size_mb <= max_size_mb:
                files_to_download.append(f)
                total_size += size_mb
        
        print(f"Will download {len(files_to_download)} files ({total_size:.1f} MB)")
        
        # Download files directly via HTTP
        downloaded_files = []
        for file_info in files_to_download:
            file_path = file_info["path"]
            asset_id = file_info.get("identifier", "")
            
            print(f"Downloading: {file_path} ({file_info.get('size_mb', 0):.1f} MB)")
            
            # Get download URL from DANDI API
            download_url = f"https://api.dandiarchive.org/api/assets/{asset_id}/download/"
            
            try:
                # Stream download to avoid memory issues
                response = requests.get(download_url, stream=True, timeout=300)
                response.raise_for_status()
                
                # Create output path preserving directory structure
                local_path = output_dir / file_path
                local_path.parent.mkdir(parents=True, exist_ok=True)
                
                with open(local_path, 'wb') as f:
                    for chunk in response.iter_content(chunk_size=8192):
                        f.write(chunk)
                
                downloaded_files.append(str(local_path))
                print(f"  Saved to: {local_path}")
                
            except Exception as e:
                print(f"  Error downloading {file_path}: {e}")
        
        if not downloaded_files:
            print("No files were downloaded successfully")
            return None
        
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
            len(downloaded_files),
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
    Uses h5py directly instead of pynwb for better compatibility.
    
    Args:
        nwb_path: Path to NWB file
        segment_duration: Duration of each segment in seconds
    
    Returns:
        List of extracted segments with neural and behavior features
    """
    try:
        import h5py
        
        segments = []
        
        with h5py.File(str(nwb_path), 'r') as f:
            # Find neural data in acquisition group
            neural_data = None
            neural_rate = 1000  # default
            neural_key = None
            
            if 'acquisition' in f:
                acq = f['acquisition']
                for name in acq.keys():
                    item = acq[name]
                    if 'data' in item:
                        neural_data = item['data'][:]
                        if 'starting_time' in item and hasattr(item['starting_time'], 'attrs'):
                            neural_rate = item['starting_time'].attrs.get('rate', 1000)
                        elif 'rate' in item.attrs:
                            neural_rate = item.attrs['rate']
                        neural_key = name
                        print(f"Found neural data: {name}, shape: {neural_data.shape}, rate: {neural_rate}")
                        break
            
            if neural_data is None:
                # Try processing/ecephys for processed neural data (e.g., ripples)
                if 'processing' in f and 'ecephys' in f['processing']:
                    ecephys = f['processing']['ecephys']
                    
                    # Look for Ripples or other processed neural events
                    if 'Ripples' in ecephys:
                        ripples = ecephys['Ripples']
                        if 'start_time' in ripples and 'peak_amplitudes' in ripples:
                            ripple_times = ripples['start_time'][:]
                            ripple_amps = ripples['peak_amplitudes'][:]
                            ripple_freqs = ripples['peak_frequencies'][:]
                            
                            print(f"Found {len(ripple_times)} ripple events")
                            
                            # Create segments based on ripple activity
                            # Start from first ripple time to avoid empty segments
                            min_time = float(np.min(ripple_times))
                            max_time = float(np.max(ripple_times))
                            total_duration = max_time - min_time
                            num_segments = int(total_duration / segment_duration)
                            
                            print(f"Ripple events span: {min_time:.1f}s to {max_time:.1f}s ({total_duration:.1f}s)")
                            
                            for i in range(min(num_segments, 200)):
                                start_time = min_time + i * segment_duration
                                end_time = start_time + segment_duration
                                
                                # Find ripples in this segment
                                mask = (ripple_times >= start_time) & (ripple_times < end_time)
                                seg_amps = ripple_amps[mask]
                                seg_freqs = ripple_freqs[mask]
                                
                                # Calculate segment features
                                ripple_rate = len(seg_amps) / segment_duration
                                mean_amp = float(np.mean(seg_amps)) if len(seg_amps) > 0 else 0
                                mean_freq = float(np.mean(seg_freqs)) if len(seg_freqs) > 0 else 0
                                
                                segment = {
                                    "start_time": start_time,
                                    "end_time": end_time,
                                    "neural_power_delta": 0,
                                    "neural_power_theta": 0,
                                    "neural_power_alpha": 0,
                                    "neural_power_beta": mean_freq / 200,  # Normalized freq
                                    "neural_power_gamma": ripple_rate,  # Ripples are gamma-range
                                    "ripple_rate": ripple_rate,
                                    "ripple_amplitude": mean_amp,
                                    "ripple_frequency": mean_freq,
                                    "behavior_state": "ripple_active" if ripple_rate > 1 else "low_ripple",
                                    "activity_level": ripple_rate / 10,  # Normalized
                                    "arousal_estimate": mean_amp / 100,  # Normalized
                                    "timestamp": datetime.utcnow().isoformat(),
                                    "has_real_lfp": False,  # This is processed data
                                    "data_type": "ripple_events"
                                }
                                segments.append(segment)
                            
                            print(f"Extracted {len(segments)} segments from ripple events")
                            return segments
                
                print(f"No usable neural data found in {nwb_path}")
                return segments
            
            # Find behavior data
            behavior_data = None
            behavior_rate = 1
            
            if 'processing' in f and 'behavior' in f['processing']:
                behavior_mod = f['processing']['behavior']
                # Look for speed, position, or other behavioral signals
                for name in ['speed', 'running_speed', 'velocity', 'position', 'BehavioralTimeSeries']:
                    if name in behavior_mod:
                        ts = behavior_mod[name]
                        if 'data' in ts:
                            behavior_data = ts['data'][:]
                            if 'rate' in ts.attrs:
                                behavior_rate = ts.attrs['rate']
                            print(f"Found behavior data: {name}, shape: {behavior_data.shape}")
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


def save_segments_to_db(segments: List[Dict[str, Any]], nwb_file_id: int) -> int:
    """Save processed segments to the database."""
    db_path = DATA_DIR / "neural_study.db"
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    count = 0
    for seg in segments:
        cursor.execute("""
            INSERT INTO neural_behavior_segments 
            (nwb_file_id, start_time, end_time, neural_power_delta, neural_power_theta,
             neural_power_alpha, neural_power_beta, neural_power_gamma,
             behavior_state, activity_level, arousal_estimate, timestamp)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            nwb_file_id,
            seg.get('start_time', 0),
            seg.get('end_time', 0),
            seg.get('neural_power_delta', 0),
            seg.get('neural_power_theta', 0),
            seg.get('neural_power_alpha', 0),
            seg.get('neural_power_beta', 0),
            seg.get('neural_power_gamma', 0),
            seg.get('behavior_state', 'unknown'),
            seg.get('activity_level', 0),
            seg.get('arousal_estimate', 0),
            seg.get('timestamp', datetime.utcnow().isoformat())
        ))
        count += 1
    
    conn.commit()
    conn.close()
    return count


def analyze_session_lcc(segments: List[Dict[str, Any]]) -> Dict[str, Any]:
    """
    Analyze LCC within a single session by examining correlations
    between neural and behavioral features across time.
    
    NOTE: For meaningful LCC analysis, neural and behavior features must come
    from independent sources. If both are derived from the same data (e.g.,
    ripple events), the correlation is tautological.
    """
    import numpy as np
    from scipy import stats
    
    if len(segments) < 10:
        return {"error": "Not enough segments for analysis", "n": len(segments)}
    
    # Check if behavior is derived from neural (tautological case)
    data_type = segments[0].get('data_type', 'unknown') if segments else 'unknown'
    is_tautological = data_type == 'ripple_events'  # activity derived from ripple_rate
    
    # Extract features - remove NaNs
    ripple_rates = np.array([s.get('ripple_rate', s.get('neural_power_gamma', 0)) for s in segments])
    activity_levels = np.array([s.get('activity_level', 0) for s in segments])
    
    # Handle NaN values
    valid_mask = ~(np.isnan(ripple_rates) | np.isnan(activity_levels))
    ripple_rates = ripple_rates[valid_mask]
    activity_levels = activity_levels[valid_mask]
    
    if len(ripple_rates) < 10:
        return {"error": "Too many NaN values, insufficient data", "n": int(np.sum(valid_mask))}
    
    # Calculate correlations
    results = {
        "n_segments": len(ripple_rates),
        "data_type": data_type,
        "is_tautological": is_tautological
    }
    
    # Neural-behavior correlation (key LCC test)
    if np.std(ripple_rates) > 0 and np.std(activity_levels) > 0:
        corr, p_val = stats.pearsonr(ripple_rates, activity_levels)
        results["neural_behavior_correlation"] = float(corr)
        results["neural_behavior_p_value"] = float(p_val)
    else:
        results["neural_behavior_correlation"] = 0
        results["neural_behavior_p_value"] = 1.0
        results["lcc_interpretation"] = "Insufficient variance for correlation analysis"
        return results
    
    # Block permutation test (LCC methodology)
    # Minimum block size of 3 to preserve local temporal structure
    n_permutations = 1000
    min_block_size = 3
    block_size = max(min_block_size, len(ripple_rates) // 10)  # ~10% of data
    results["block_size"] = block_size
    
    observed_corr = results["neural_behavior_correlation"]
    
    null_correlations = []
    n = len(ripple_rates)
    
    for _ in range(n_permutations):
        # Block shuffle that handles remainder properly
        n_complete_blocks = n // block_size
        remainder = n % block_size
        
        # Create blocks including partial final block
        blocks = []
        for i in range(n_complete_blocks):
            blocks.append(ripple_rates[i*block_size:(i+1)*block_size])
        if remainder > 0:
            blocks.append(ripple_rates[n_complete_blocks*block_size:])
        
        # Shuffle block order
        np.random.shuffle(blocks)
        
        # Reconstruct shuffled array
        shuffled_neural = np.concatenate(blocks)
        
        if len(shuffled_neural) == len(activity_levels) and np.std(shuffled_neural) > 0:
            null_corr, _ = stats.pearsonr(shuffled_neural, activity_levels)
            null_correlations.append(null_corr)
    
    if len(null_correlations) >= 100:  # Need sufficient permutations
        null_correlations = np.array(null_correlations)
        permutation_p = np.mean(np.abs(null_correlations) >= np.abs(observed_corr))
        results["permutation_p_value"] = float(permutation_p)
        results["null_mean"] = float(np.mean(null_correlations))
        results["null_std"] = float(np.std(null_correlations))
        
        # Calculate effect size (Cohen's d)
        null_std = np.std(null_correlations)
        if null_std > 0:
            cohens_d = (observed_corr - np.mean(null_correlations)) / null_std
            results["effect_size"] = float(cohens_d)
        else:
            results["effect_size"] = None
    else:
        results["permutation_p_value"] = None
        results["permutation_warning"] = "Insufficient valid permutations for statistical test"
    
    # LCC interpretation
    if is_tautological:
        results["lcc_interpretation"] = (
            "TAUTOLOGICAL: Behavior features derived from neural data. "
            "High correlation expected but not meaningful for LCC testing. "
            "Requires independent behavior signal (e.g., movement, stimuli)."
        )
    elif results.get("permutation_p_value") is None:
        results["lcc_interpretation"] = "Insufficient permutations for LCC interpretation"
    elif results["permutation_p_value"] < 0.05:
        if observed_corr > 0.3:
            results["lcc_interpretation"] = "Strong local causation (LCC ≈ 1)"
        elif observed_corr > 0.1:
            results["lcc_interpretation"] = "Moderate local causation (LCC > 0.5)"
        else:
            results["lcc_interpretation"] = "Weak but significant correlation"
    else:
        if observed_corr < -0.1 and results.get("permutation_p_value", 1) < 0.1:
            results["lcc_interpretation"] = "Potential non-local correlation (LCC < 1) - requires validation"
        else:
            results["lcc_interpretation"] = "No significant neural-behavior correlation"
    
    return results


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
