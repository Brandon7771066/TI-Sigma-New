"""
Allen Brain Observatory Integration for LCC Studies

Accesses mouse neural activity + behavior data from Allen Institute.
Uses AllenSDK to download Visual Behavior Neuropixels data.

Key datasets:
- Visual Behavior Neuropixels: 153 sessions, 81 mice
- Neural spiking + LFP during visual change detection task
- Behavior: running speed, licks, rewards, trials
"""

import os
import sys
import json
import sqlite3
from pathlib import Path
from datetime import datetime
from dataclasses import dataclass
from typing import Dict, List, Optional, Any
import numpy as np

# Database path (shared with DANDI integration)
DATA_DIR = Path(__file__).parent / "neural_data"
ALLEN_CACHE_DIR = DATA_DIR / "allen_cache"
DB_PATH = DATA_DIR / "neural_study.db"


def check_allensdk():
    """Check if AllenSDK is installed"""
    try:
        import allensdk
        return True
    except ImportError:
        return False


def install_allensdk():
    """Install AllenSDK"""
    import subprocess
    print("Installing AllenSDK...")
    try:
        subprocess.run(
            [sys.executable, "-m", "pip", "install", "allensdk"],
            check=True,
            capture_output=True
        )
        print("AllenSDK installed successfully")
        return True
    except subprocess.CalledProcessError as e:
        print(f"Failed to install AllenSDK: {e}")
        return False


def get_visual_behavior_sessions() -> List[Dict[str, Any]]:
    """
    Get list of available Visual Behavior Neuropixels sessions.
    
    Returns metadata about each session including:
    - session_id
    - mouse_id
    - genotype
    - structure (brain regions)
    - behavior task info
    """
    if not check_allensdk():
        if not install_allensdk():
            return [{"error": "AllenSDK not available"}]
    
    ALLEN_CACHE_DIR.mkdir(parents=True, exist_ok=True)
    
    try:
        from allensdk.brain_observatory.ecephys.ecephys_project_cache import EcephysProjectCache
        
        cache = EcephysProjectCache.from_warehouse(
            manifest=str(ALLEN_CACHE_DIR / "ecephys_manifest.json")
        )
        
        sessions_df = cache.get_session_table()
        
        sessions = []
        for session_id, row in sessions_df.iterrows():
            sessions.append({
                "session_id": int(session_id),
                "specimen_id": int(row.get("specimen_id", 0)) if "specimen_id" in row else None,
                "genotype": row.get("full_genotype", "unknown"),
                "session_type": row.get("session_type", "unknown"),
                "structure_acronyms": row.get("ecephys_structure_acronyms", []),
                "unit_count": int(row.get("unit_count", 0)) if "unit_count" in row else 0
            })
        
        print(f"Found {len(sessions)} Visual Coding sessions")
        return sessions[:50]  # Return first 50 for efficiency
        
    except Exception as e:
        print(f"Error getting sessions: {e}")
        return [{"error": str(e)}]


def download_session_data(session_id: int) -> Optional[Dict[str, Any]]:
    """
    Download data for a specific session.
    
    Returns dict with neural and behavior data paths.
    """
    if not check_allensdk():
        return None
    
    ALLEN_CACHE_DIR.mkdir(parents=True, exist_ok=True)
    
    try:
        from allensdk.brain_observatory.ecephys.ecephys_project_cache import EcephysProjectCache
        
        cache = EcephysProjectCache.from_warehouse(
            manifest=str(ALLEN_CACHE_DIR / "ecephys_manifest.json")
        )
        
        print(f"Downloading session {session_id}...")
        session = cache.get_session_data(session_id)
        
        # Get basic info
        info = {
            "session_id": session_id,
            "units": len(session.units) if hasattr(session, 'units') else 0,
            "channels": len(session.channels) if hasattr(session, 'channels') else 0,
            "probes": len(session.probes) if hasattr(session, 'probes') else 0,
            "has_running_speed": hasattr(session, 'running_speed'),
            "stimulus_presentations": len(session.stimulus_presentations) if hasattr(session, 'stimulus_presentations') else 0
        }
        
        # Record in database
        conn = sqlite3.connect(str(DB_PATH))
        cursor = conn.cursor()
        cursor.execute("""
            INSERT OR REPLACE INTO downloaded_datasets 
            (dandiset_id, name, species, download_date, local_path, num_files, total_size_mb, status)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            f"allen_{session_id}",
            f"Allen Visual Coding Session {session_id}",
            "Mus musculus",
            datetime.utcnow().isoformat(),
            str(ALLEN_CACHE_DIR),
            1,
            0,  # Size not easily available
            "completed"
        ))
        conn.commit()
        conn.close()
        
        print(f"Session {session_id} ready: {info['units']} units, {info['channels']} channels")
        return info
        
    except Exception as e:
        print(f"Error downloading session {session_id}: {e}")
        return None


def process_allen_session_for_lcc(session_id: int, segment_duration: float = 30.0) -> List[Dict[str, Any]]:
    """
    Process an Allen Brain session to extract neural-behavior segments.
    
    Uses actual LFP data for band power calculation when available.
    Falls back to firing rate metrics if LFP not accessible.
    
    Args:
        session_id: Allen session ID
        segment_duration: Duration of each segment in seconds
    
    Returns:
        List of extracted segments with neural and behavior features
    """
    if not check_allensdk():
        return []
    
    try:
        from allensdk.brain_observatory.ecephys.ecephys_project_cache import EcephysProjectCache
        
        cache = EcephysProjectCache.from_warehouse(
            manifest=str(ALLEN_CACHE_DIR / "ecephys_manifest.json")
        )
        
        session = cache.get_session_data(session_id)
        
        segments = []
        
        # Try to get LFP data for real band power calculation
        lfp_data = None
        lfp_times = None  # Timestamps for LFP alignment
        lfp_rate = 2500  # Allen LFP is 2.5 kHz
        
        try:
            probes = session.probes
            if len(probes) > 0:
                probe_id = probes.index[0]
                lfp = session.get_lfp(probe_id)
                if lfp is not None:
                    # Handle xarray vs numpy
                    if hasattr(lfp, 'values'):
                        lfp_data = lfp.values
                        # Get time coordinate for alignment
                        if hasattr(lfp, 'time'):
                            lfp_times = lfp.time.values
                        elif hasattr(lfp, 'coords') and 'time' in lfp.coords:
                            lfp_times = lfp.coords['time'].values
                    else:
                        lfp_data = lfp
                    
                    print(f"Loaded LFP data: shape {lfp_data.shape if hasattr(lfp_data, 'shape') else 'unknown'}")
                    if lfp_times is not None:
                        print(f"LFP time range: {lfp_times[0]:.2f} - {lfp_times[-1]:.2f}s")
        except Exception as e:
            print(f"Could not load LFP: {e}")
        
        # Get running speed as behavior measure
        if hasattr(session, 'running_speed'):
            running_speed = session.running_speed
            
            if 'velocity' in running_speed.columns:
                speed_data = running_speed['velocity'].values
                time_data = running_speed.index.values
                
                # Get total duration
                total_duration = float(time_data[-1] - time_data[0])
                num_segments = int(total_duration / segment_duration)
                
                # Get spike times for neural activity (backup if no LFP)
                spike_times = session.spike_times
                unit_ids = list(spike_times.keys())[:10]  # Use first 10 units
                
                for i in range(min(num_segments, 100)):
                    start_time = float(time_data[0]) + i * segment_duration
                    end_time = start_time + segment_duration
                    
                    # Calculate mean running speed in segment
                    mask = (time_data >= start_time) & (time_data < end_time)
                    if np.sum(mask) > 0:
                        segment_speed = speed_data[mask]
                        activity_level = float(np.mean(np.abs(segment_speed)))
                        arousal_estimate = float(np.std(segment_speed))
                    else:
                        activity_level = 0
                        arousal_estimate = 0
                    
                    # Calculate band powers from LFP if available
                    if lfp_data is not None:
                        # Use timestamp alignment if available
                        if lfp_times is not None:
                            # Find LFP samples within this time segment
                            lfp_mask = (lfp_times >= start_time) & (lfp_times < end_time)
                            if np.sum(lfp_mask) > 100:  # Need sufficient samples
                                lfp_segment = lfp_data[lfp_mask]
                                powers = calculate_lfp_band_powers(lfp_segment, lfp_rate)
                            else:
                                powers = {"delta": 0, "theta": 0, "alpha": 0, "beta": 0, "gamma": 0}
                        else:
                            # Fall back to index-based extraction
                            lfp_start = int(start_time * lfp_rate)
                            lfp_end = int(end_time * lfp_rate)
                            n_samples = lfp_data.shape[0] if len(lfp_data.shape) > 0 else len(lfp_data)
                            if lfp_end <= n_samples:
                                lfp_segment = lfp_data[lfp_start:lfp_end]
                                powers = calculate_lfp_band_powers(lfp_segment, lfp_rate)
                            else:
                                powers = {"delta": 0, "theta": 0, "alpha": 0, "beta": 0, "gamma": 0}
                    else:
                        # Fallback: use firing rate variability as proxy
                        total_spikes = 0
                        spike_counts = []
                        for uid in unit_ids:
                            spikes = spike_times[uid]
                            segment_spikes = spikes[(spikes >= start_time) & (spikes < end_time)]
                            spike_counts.append(len(segment_spikes))
                            total_spikes += len(segment_spikes)
                        
                        avg_firing_rate = total_spikes / (len(unit_ids) * segment_duration) if unit_ids else 0
                        firing_variance = float(np.var(spike_counts)) if spike_counts else 0
                        
                        # Store as zeros - proxy values go in separate fields
                        powers = {
                            "delta": 0,
                            "theta": 0,
                            "alpha": 0,
                            "beta": 0,
                            "gamma": 0
                        }
                    
                    # Calculate spike-based proxies (stored separately from LFP powers)
                    total_spikes = 0
                    spike_counts = []
                    for uid in unit_ids:
                        spikes = spike_times[uid]
                        segment_spikes = spikes[(spikes >= start_time) & (spikes < end_time)]
                        spike_counts.append(len(segment_spikes))
                        total_spikes += len(segment_spikes)
                    
                    avg_firing_rate = total_spikes / (len(unit_ids) * segment_duration) if unit_ids else 0
                    firing_variance = float(np.var(spike_counts)) if spike_counts else 0
                    
                    segment = {
                        "start_time": start_time,
                        "end_time": end_time,
                        "neural_power_delta": powers["delta"],
                        "neural_power_theta": powers["theta"],
                        "neural_power_alpha": powers["alpha"],
                        "neural_power_beta": powers["beta"],
                        "neural_power_gamma": powers["gamma"],
                        "spike_firing_rate": avg_firing_rate,  # Separate proxy field
                        "spike_variance": firing_variance,  # Separate proxy field
                        "behavior_state": classify_behavior_state(activity_level),
                        "activity_level": activity_level,
                        "arousal_estimate": arousal_estimate,
                        "has_real_lfp": lfp_data is not None,
                        "timestamp": datetime.utcnow().isoformat()
                    }
                    segments.append(segment)
        
        print(f"Extracted {len(segments)} segments from Allen session {session_id} (LFP: {lfp_data is not None})")
        return segments
        
    except Exception as e:
        print(f"Error processing Allen session {session_id}: {e}")
        return []


def calculate_lfp_band_powers(lfp_segment: np.ndarray, sampling_rate: float = 2500) -> Dict[str, float]:
    """
    Calculate power spectral density in standard EEG/LFP frequency bands.
    
    Uses Welch's method for robust PSD estimation.
    
    Bands:
        delta: 0.5-4 Hz
        theta: 4-8 Hz
        alpha: 8-13 Hz
        beta: 13-30 Hz
        gamma: 30-100 Hz
    """
    try:
        from scipy import signal as scipy_signal
        
        # If multi-channel, average across channels
        if len(lfp_segment.shape) > 1:
            lfp_segment = np.mean(lfp_segment, axis=1)
        
        # Compute power spectral density using Welch's method
        nperseg = min(len(lfp_segment), int(sampling_rate * 2))  # 2-second windows
        freqs, psd = scipy_signal.welch(lfp_segment, fs=sampling_rate, nperseg=nperseg)
        
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
        return {"delta": 0, "theta": 0, "alpha": 0, "beta": 0, "gamma": 0}
    except Exception as e:
        print(f"Error calculating band powers: {e}")
        return {"delta": 0, "theta": 0, "alpha": 0, "beta": 0, "gamma": 0}


def classify_behavior_state(activity_level: float) -> str:
    """Classify behavior state based on activity level"""
    if activity_level < 1:
        return "rest"
    elif activity_level < 5:
        return "low_activity"
    elif activity_level < 20:
        return "moderate_activity"
    else:
        return "high_activity"


def get_allen_lfp_data(session_id: int, probe_id: Optional[int] = None) -> Optional[Dict[str, Any]]:
    """
    Get LFP data from an Allen session.
    
    LFP is available at 2.5 kHz for frequency analysis.
    """
    if not check_allensdk():
        return None
    
    try:
        from allensdk.brain_observatory.ecephys.ecephys_project_cache import EcephysProjectCache
        
        cache = EcephysProjectCache.from_warehouse(
            manifest=str(ALLEN_CACHE_DIR / "ecephys_manifest.json")
        )
        
        session = cache.get_session_data(session_id)
        
        # Get probe info
        probes = session.probes
        if probe_id is None and len(probes) > 0:
            probe_id = probes.index[0]
        
        if probe_id is None:
            return None
        
        # Get LFP for probe
        lfp = session.get_lfp(probe_id)
        
        info = {
            "session_id": session_id,
            "probe_id": int(probe_id),
            "sampling_rate": 2500,  # Allen LFP is 2.5 kHz
            "channels": lfp.shape[1] if len(lfp.shape) > 1 else 1,
            "duration_seconds": len(lfp) / 2500,
            "shape": lfp.shape
        }
        
        return info
        
    except Exception as e:
        print(f"Error getting LFP from session {session_id}: {e}")
        return None


def run_cross_session_lcc_analysis(session_ids: List[int]) -> Dict[str, Any]:
    """
    Run LCC analysis across multiple Allen sessions.
    
    Tests whether mouse behavior/neural patterns correlate across
    different sessions (which would be surprising under LCC=1).
    
    Methodology:
    1. Extract synchronized neural (LFP band power) + behavior (running speed) segments
    2. Compute pairwise correlations between sessions for both neural and behavior
    3. Generate null distribution via block permutation testing (preserves autocorrelation)
    4. Report effect sizes with interpretation
    
    Limitations (acknowledged for exploratory analysis):
    - Timebase alignment assumes shared absolute time; may have offset errors
    - No explicit control for stimulus epochs or task structure
    - Neural correlations only computed when BOTH sessions have real LFP
    - Block permutation preserves short-range autocorrelation but not nonstationarity
    - Any significant correlations should be investigated for confounds before LCC claims
    """
    all_segments = []
    
    for session_id in session_ids:
        segments = process_allen_session_for_lcc(session_id)
        for seg in segments:
            seg["session_id"] = session_id
        all_segments.extend(segments)
    
    if len(all_segments) < 20:
        return {"error": "Insufficient data", "segments": len(all_segments)}
    
    # Group by session
    session_data = {}
    for seg in all_segments:
        sid = seg["session_id"]
        if sid not in session_data:
            session_data[sid] = []
        session_data[sid].append(seg)
    
    from scipy.stats import pearsonr, spearmanr
    
    results = []
    session_list = list(session_data.keys())
    
    for i in range(len(session_list)):
        for j in range(i + 1, len(session_list)):
            sid_a = session_list[i]
            sid_b = session_list[j]
            
            segs_a = session_data[sid_a]
            segs_b = session_data[sid_b]
            
            min_len = min(len(segs_a), len(segs_b))
            if min_len < 10:
                continue
            
            # Extract features
            activity_a = np.array([s["activity_level"] for s in segs_a[:min_len]])
            activity_b = np.array([s["activity_level"] for s in segs_b[:min_len]])
            
            theta_a = np.array([s["neural_power_theta"] for s in segs_a[:min_len]])
            theta_b = np.array([s["neural_power_theta"] for s in segs_b[:min_len]])
            
            gamma_a = np.array([s["neural_power_gamma"] for s in segs_a[:min_len]])
            gamma_b = np.array([s["neural_power_gamma"] for s in segs_b[:min_len]])
            
            # Check for real LFP data in BOTH sessions
            has_lfp_a = any(s.get("has_real_lfp", False) for s in segs_a[:min_len])
            has_lfp_b = any(s.get("has_real_lfp", False) for s in segs_b[:min_len])
            both_have_lfp = has_lfp_a and has_lfp_b
            
            pair_result = {
                "session_a": sid_a,
                "session_b": sid_b,
                "n": min_len,
                "has_real_lfp_a": has_lfp_a,
                "has_real_lfp_b": has_lfp_b,
                "both_have_lfp": both_have_lfp
            }
            
            # Behavior correlation
            if np.std(activity_a) > 0 and np.std(activity_b) > 0:
                r_behavior, p_behavior = pearsonr(activity_a, activity_b)
                pair_result["behavior_r"] = float(r_behavior)
                pair_result["behavior_p"] = float(p_behavior)
            else:
                pair_result["behavior_r"] = 0
                pair_result["behavior_p"] = 1
            
            # Neural correlations (only computed when BOTH sessions have real LFP)
            if both_have_lfp and np.std(theta_a) > 0 and np.std(theta_b) > 0:
                r_theta, p_theta = pearsonr(theta_a, theta_b)
                pair_result["theta_r"] = float(r_theta)
                pair_result["theta_p"] = float(p_theta)
                pair_result["theta_valid"] = True
            else:
                pair_result["theta_r"] = None  # Explicitly null, not zero
                pair_result["theta_p"] = None
                pair_result["theta_valid"] = False
            
            if both_have_lfp and np.std(gamma_a) > 0 and np.std(gamma_b) > 0:
                r_gamma, p_gamma = pearsonr(gamma_a, gamma_b)
                pair_result["gamma_r"] = float(r_gamma)
                pair_result["gamma_p"] = float(p_gamma)
                pair_result["gamma_valid"] = True
            else:
                pair_result["gamma_r"] = None
                pair_result["gamma_p"] = None
                pair_result["gamma_valid"] = False
            
            # Block permutation test for behavior (preserves autocorrelation)
            n_permutations = 1000
            block_size = max(5, min_len // 10)  # ~10% of data as block size
            null_correlations = []
            
            for _ in range(n_permutations):
                # Block shuffle to preserve local time structure
                n_blocks = int(np.ceil(min_len / block_size))
                block_order = np.random.permutation(n_blocks)
                shuffled_b = []
                for block_idx in block_order:
                    start = block_idx * block_size
                    end = min(start + block_size, min_len)
                    shuffled_b.extend(activity_b[start:end])
                shuffled_b = np.array(shuffled_b[:min_len])
                
                if len(shuffled_b) == min_len:
                    r_null, _ = pearsonr(activity_a, shuffled_b)
                    null_correlations.append(r_null)
            
            if null_correlations:
                null_correlations = np.array(null_correlations)
                pair_result["permutation_p"] = float(np.mean(np.abs(null_correlations) >= np.abs(pair_result["behavior_r"])))
                pair_result["null_mean"] = float(np.mean(null_correlations))
                pair_result["null_std"] = float(np.std(null_correlations))
                pair_result["block_size"] = block_size
            else:
                pair_result["permutation_p"] = 1.0
                pair_result["null_mean"] = 0.0
                pair_result["null_std"] = 0.0
            
            results.append(pair_result)
    
    # Summary statistics
    if results:
        behavior_rs = [r["behavior_r"] for r in results]
        avg_behavior_r = np.mean(behavior_rs)
        
        # Count significant results
        sig_pearson = len([r for r in results if r["behavior_p"] < 0.05])
        sig_permutation = len([r for r in results if r["permutation_p"] < 0.05])
        
        # Effect size interpretation
        if np.abs(avg_behavior_r) < 0.1:
            effect_interpretation = "negligible"
        elif np.abs(avg_behavior_r) < 0.3:
            effect_interpretation = "small"
        elif np.abs(avg_behavior_r) < 0.5:
            effect_interpretation = "medium"
        else:
            effect_interpretation = "large"
        
        interpretation = (
            f"Tested {len(results)} session pairs. "
            f"Average behavior correlation: r={avg_behavior_r:.3f} ({effect_interpretation} effect). "
            f"Significant by Pearson: {sig_pearson}/{len(results)}. "
            f"Significant by permutation test: {sig_permutation}/{len(results)}. "
        )
        
        if sig_permutation == 0:
            interpretation += "Result is consistent with LCC=1 (no non-local correlation)."
        elif sig_permutation / len(results) < 0.1:
            interpretation += "Few significant pairs (~expected false positive rate). Consistent with LCC=1."
        else:
            interpretation += "More significant pairs than expected by chance. Investigate confounds before claiming LCC<1."
        
        return {
            "num_pairs": len(results),
            "average_behavior_r": float(avg_behavior_r),
            "effect_size": effect_interpretation,
            "significant_pearson": sig_pearson,
            "significant_permutation": sig_permutation,
            "interpretation": interpretation,
            "methodology": "Pearson correlation + permutation test (1000 permutations) for behavior synchrony",
            "details": results
        }
    else:
        return {"error": "No valid session pairs for analysis"}


def autonomous_lcc_pipeline(num_sessions: int = 3) -> Dict[str, Any]:
    """
    Run fully autonomous LCC analysis pipeline.
    
    1. Gets available Allen sessions
    2. Downloads first N sessions
    3. Processes neural + behavior data
    4. Runs cross-session LCC analysis
    5. Returns results with interpretation
    
    This is the main entry point for autonomous operation.
    """
    print("=" * 60)
    print("AUTONOMOUS LCC ANALYSIS PIPELINE")
    print("=" * 60)
    
    # Step 1: Get available sessions
    print("\n[Step 1] Getting available sessions...")
    sessions = get_visual_behavior_sessions()
    
    if not sessions or "error" in sessions[0]:
        return {"error": "Failed to get sessions", "details": sessions}
    
    print(f"Found {len(sessions)} sessions")
    
    # Step 2: Select sessions with most units
    sessions_with_units = [s for s in sessions if s.get("unit_count", 0) > 100]
    sessions_with_units.sort(key=lambda x: x.get("unit_count", 0), reverse=True)
    
    selected_sessions = [s["session_id"] for s in sessions_with_units[:num_sessions]]
    print(f"Selected sessions: {selected_sessions}")
    
    # Step 3: Download sessions
    print("\n[Step 2] Downloading session data...")
    for sid in selected_sessions:
        info = download_session_data(sid)
        if info:
            print(f"  Session {sid}: {info.get('units', 0)} units")
    
    # Step 4: Process for LCC
    print("\n[Step 3] Processing neural + behavior data...")
    
    # Save segments to database
    conn = sqlite3.connect(str(DB_PATH))
    cursor = conn.cursor()
    
    for sid in selected_sessions:
        segments = process_allen_session_for_lcc(sid)
        
        # Get or create NWB file entry
        cursor.execute("""
            INSERT OR IGNORE INTO nwb_files 
            (dandiset_id, file_path, subject_id, session_id, has_neural_data, has_behavior_data, processed)
            VALUES (?, ?, ?, ?, ?, ?, ?)
        """, (f"allen_{sid}", f"allen_session_{sid}", f"mouse_{sid}", str(sid), True, True, True))
        
        cursor.execute("SELECT id FROM nwb_files WHERE session_id = ?", (str(sid),))
        row = cursor.fetchone()
        nwb_file_id = row[0] if row else 1
        
        # Save segments
        for seg in segments:
            cursor.execute("""
                INSERT INTO neural_behavior_segments 
                (nwb_file_id, start_time, end_time, neural_power_delta, neural_power_theta,
                 neural_power_alpha, neural_power_beta, neural_power_gamma,
                 behavior_state, activity_level, arousal_estimate, timestamp)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                nwb_file_id, seg["start_time"], seg["end_time"],
                seg["neural_power_delta"], seg["neural_power_theta"],
                seg["neural_power_alpha"], seg["neural_power_beta"], seg["neural_power_gamma"],
                seg["behavior_state"], seg["activity_level"], seg["arousal_estimate"],
                seg["timestamp"]
            ))
    
    conn.commit()
    conn.close()
    
    # Step 5: Run LCC analysis
    print("\n[Step 4] Running cross-session LCC analysis...")
    results = run_cross_session_lcc_analysis(selected_sessions)
    
    print("\n" + "=" * 60)
    print("ANALYSIS COMPLETE")
    print("=" * 60)
    print(f"\nResults: {json.dumps(results, indent=2)}")
    
    return results


if __name__ == "__main__":
    print("Allen Brain Observatory Integration for LCC Studies")
    print("=" * 50)
    
    # Check SDK
    if check_allensdk():
        print("AllenSDK is installed")
    else:
        print("AllenSDK not found - will install on first use")
    
    print("\nTo run autonomous analysis:")
    print("  from allen_brain_integration import autonomous_lcc_pipeline")
    print("  results = autonomous_lcc_pipeline(num_sessions=3)")
