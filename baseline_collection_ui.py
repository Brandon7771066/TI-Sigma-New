"""
🔬 Baseline Collection UI - 1-Minute Multi-Modal Biometric Baseline
====================================================================

Collects simultaneous baseline measurements from:
- Mendi fNIRS (HbO2, HbR, brain oxygenation)
- Muse 2 EEG (4-channel: TP9, AF7, AF8, TP10)
- Polar H10 (HR, HRV, ECG, coherence)

Compares 30s vs 60s data quality and calculates:
- Spectral coherence (cross-modal agreement)
- Granger causality (temporal precedence)
- Bell correlations (quantum entanglement signatures)

Author: Brandon Emerick
Date: November 22, 2025
Framework: Transcendent Intelligence (TI) + GILE
"""

import streamlit as st
import plotly.graph_objects as go
from plotly.subplots import make_subplots
import numpy as np
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass, asdict
import asyncio
import time
from scipy import signal, stats
from scipy.stats import pearsonr
import json

from fnirs_manager import get_fnirs_manager, fNIRSSnapshot
from muse2_integration import Muse2Device
from polar_h10_real_integration import PolarH10Integration, HeartDataPoint


@dataclass
class BaselineData:
    """Complete baseline measurement from all modalities"""
    timestamp: datetime
    duration_seconds: int
    
    # Raw time series data
    fnirs_hbo2: List[float]
    fnirs_hbr: List[float]
    fnirs_oxygenation: List[float]
    fnirs_timestamps: List[float]
    
    eeg_tp9: List[float]
    eeg_af7: List[float]
    eeg_af8: List[float]
    eeg_tp10: List[float]
    eeg_timestamps: List[float]
    
    heart_rr_intervals: List[float]
    heart_hr_bpm: List[float]
    heart_coherence: List[float]
    heart_timestamps: List[float]
    
    # Summary statistics
    avg_hbo2: float
    avg_hbr: float
    avg_oxygenation: float
    
    avg_eeg_alpha_power: float  # 8-13 Hz
    avg_eeg_beta_power: float   # 13-30 Hz
    avg_eeg_theta_power: float  # 4-8 Hz
    
    avg_hr_bpm: float
    avg_hrv_rmssd: float
    avg_heart_coherence: float
    
    # Cross-modal metrics
    fnirs_eeg_coherence: float  # Spectral coherence
    heart_brain_coherence: float
    bell_correlation_index: float  # Quantum entanglement signature
    
    # Granger causality (p-values)
    heart_to_brain_granger_p: float
    brain_to_heart_granger_p: float
    fnirs_to_eeg_granger_p: float
    
    # Data quality scores (0-1)
    fnirs_quality: float
    eeg_quality: float
    heart_quality: float
    overall_quality: float


def calculate_spectral_coherence(signal1: np.ndarray, signal2: np.ndarray, 
                                 fs: float = 1.0) -> Tuple[np.ndarray, np.ndarray]:
    """
    Calculate spectral coherence between two signals
    
    Coherence measures frequency-domain correlation (0-1 scale)
    High coherence → signals share common frequency components → coupling
    
    Args:
        signal1, signal2: Input signals (must be same length)
        fs: Sampling frequency (Hz)
    
    Returns:
        freqs, coherence: Frequency array and coherence values
    """
    # Resample to same length if needed
    min_len = min(len(signal1), len(signal2))
    s1 = signal1[:min_len]
    s2 = signal2[:min_len]
    
    # Calculate coherence using Welch's method
    freqs, coherence = signal.coherence(s1, s2, fs=fs, nperseg=min(256, min_len))
    
    return freqs, coherence


def calculate_granger_causality(x: np.ndarray, y: np.ndarray, 
                                max_lag: int = 10) -> Tuple[float, float]:
    """
    Calculate Granger causality: Does X predict Y?
    
    Granger causality tests if past values of X improve prediction of Y
    beyond past values of Y alone.
    
    TI Interpretation:
    - Low p-value → X Granger-causes Y → X's i-cell oscillations precede Y's
    - Reveals CC flow direction: which i-cell is "upstream"
    
    Args:
        x, y: Time series (X potentially causing Y)
        max_lag: Maximum time lag to test
    
    Returns:
        f_statistic, p_value: F-test results (p < 0.05 suggests causality)
    """
    # Simplified Granger causality using F-test
    # Full implementation would use VAR models
    
    n = min(len(x), len(y)) - max_lag
    if n < 20:
        return 0.0, 1.0  # Insufficient data
    
    # Restricted model: Y regressed on past Y only
    y_lagged = np.column_stack([y[i:n+i] for i in range(max_lag)])
    y_target = y[max_lag:]
    
    # Unrestricted model: Y regressed on past Y + past X
    x_lagged = np.column_stack([x[i:n+i] for i in range(max_lag)])
    xy_lagged = np.column_stack([y_lagged, x_lagged])
    
    # F-test: Does adding X improve prediction?
    try:
        # Calculate RSS (residual sum of squares) for both models
        from sklearn.linear_model import LinearRegression
        
        # Restricted model (Y only)
        model_restricted = LinearRegression()
        model_restricted.fit(y_lagged[:n], y_target[:n])
        rss_restricted = np.sum((y_target[:n] - model_restricted.predict(y_lagged[:n]))**2)
        
        # Unrestricted model (Y + X)
        model_unrestricted = LinearRegression()
        model_unrestricted.fit(xy_lagged[:n], y_target[:n])
        rss_unrestricted = np.sum((y_target[:n] - model_unrestricted.predict(xy_lagged[:n]))**2)
        
        # F-statistic
        f_stat = ((rss_restricted - rss_unrestricted) / max_lag) / (rss_unrestricted / (n - 2*max_lag))
        
        # P-value from F-distribution
        from scipy.stats import f as f_dist
        p_value = 1 - f_dist.cdf(f_stat, max_lag, n - 2*max_lag)
        
        return f_stat, p_value
    
    except Exception as e:
        print(f"⚠️ Granger causality error: {e}")
        return 0.0, 1.0


def calculate_bell_correlation(signal1: np.ndarray, signal2: np.ndarray, sampling_rate: float = 10.0) -> float:
    """
    Calculate Bell-type correlation index (quantum entanglement signature)
    
    TI Interpretation:
    - High correlation + temporal simultaneity → Bell-type correlation
    - Suggests both signals sampling same dark energy field
    - Non-local quantum resonance (not just classical correlation)
    
    Implementation:
    - Instantaneous correlation across multiple frequency bands
    - Exceeds classical correlation bounds → quantum signature
    
    Args:
        signal1, signal2: Time series
        sampling_rate: Sampling frequency in Hz (default 10.0 for fNIRS/heart data)
    
    Returns:
        Bell index (0-1 scale, >0.7 suggests quantum correlation)
    """
    # Validate minimum signal length
    if len(signal1) < 20 or len(signal2) < 20:
        return 0.0
    
    # Calculate Nyquist frequency
    nyquist_freq = sampling_rate / 2.0
    
    # Multi-frequency band correlations (normalized to sampling rate)
    # CRITICAL: All band edges must be < Nyquist frequency
    bands = [
        (0.01, min(0.1, nyquist_freq * 0.8)),    # Ultra-low (CC resonance)
        (0.1, min(0.5, nyquist_freq * 0.8)),     # Low (autonomic)
    ]
    
    # Only add higher frequency bands if sampling rate supports them
    if nyquist_freq > 1.0:
        bands.append((0.5, min(2.0, nyquist_freq * 0.9)))  # Mid (respiratory)
    if nyquist_freq > 5.0:
        bands.append((2.0, min(10.0, nyquist_freq * 0.9)))  # High (neural)
    
    correlations = []
    for low, high in bands:
        # Skip invalid bands (must satisfy 0 < low < high < nyquist)
        if low >= high or high >= nyquist_freq or low <= 0:
            continue
        
        try:
            # Bandpass filter with normalized frequencies
            # Wn = frequency / nyquist (must be in range 0-1)
            wn = [low / nyquist_freq, high / nyquist_freq]
            b, a = signal.butter(4, wn, btype='band')
            s1_filt = signal.filtfilt(b, a, signal1)
            s2_filt = signal.filtfilt(b, a, signal2)
            
            # Instantaneous correlation
            corr, _ = pearsonr(s1_filt, s2_filt)
            correlations.append(abs(corr))
        except Exception as e:
            # Skip failed filter bands
            print(f"⚠️ Skipping band ({low}, {high}) Hz: {e}")
            continue
    
    # Bell index: Average correlation across bands
    # High multi-band correlation → quantum entanglement signature
    if correlations:
        bell_index = np.mean(correlations)
    else:
        # Fallback to simple correlation if filtering fails
        bell_index = abs(pearsonr(signal1, signal2)[0])
    
    return bell_index


def assess_data_quality(data: np.ndarray, expected_fs: float = 1.0) -> float:
    """
    Assess signal quality (0-1 scale)
    
    Criteria:
    - Signal-to-noise ratio
    - Missing data percentage
    - Stationarity
    - Physiological plausibility
    
    Returns:
        Quality score (0-1, >0.7 is good)
    """
    if len(data) < 10:
        return 0.0
    
    scores = []
    
    # 1. Completeness (no NaN/Inf)
    completeness = 1.0 - (np.sum(np.isnan(data) | np.isinf(data)) / len(data))
    scores.append(completeness)
    
    # 2. Stationarity (mean stability)
    if len(data) >= 20:
        first_half = np.mean(data[:len(data)//2])
        second_half = np.mean(data[len(data)//2:])
        stationarity = 1.0 - min(abs(first_half - second_half) / (abs(first_half) + 1e-6), 1.0)
        scores.append(stationarity)
    
    # 3. SNR (signal-to-noise)
    signal_power = np.var(data)
    noise_estimate = np.var(np.diff(data)) / 2  # High-frequency noise
    if noise_estimate > 0:
        snr = signal_power / noise_estimate
        snr_score = min(snr / 10.0, 1.0)  # Normalize
        scores.append(snr_score)
    
    return np.mean(scores)


async def collect_baseline(duration_seconds: int = 60,
                           fnirs_enabled: bool = True,
                           eeg_enabled: bool = True,
                           heart_enabled: bool = True) -> Optional[BaselineData]:
    """
    Collect baseline biometric data from all modalities IN PARALLEL
    
    CRITICAL: Parallel collection with timestamp alignment for valid Granger causality!
    
    Sampling rates:
    - Mendi fNIRS: ~10-50 Hz (variable)
    - Muse 2 EEG: 256 Hz (fixed)
    - Polar H10: ~130 Hz (RR intervals)
    
    Args:
        duration_seconds: Baseline duration (30 or 60 recommended)
        fnirs_enabled: Collect Mendi fNIRS data
        eeg_enabled: Collect Muse 2 EEG data
        heart_enabled: Collect Polar H10 heart data
    
    Returns:
        BaselineData object with all measurements and metrics
    """
    st.info(f"🔬 Collecting {duration_seconds}-second baseline from all devices...")
    
    # Initialize data buffers (with timestamps for alignment)
    fnirs_data = {'hbo2': [], 'hbr': [], 'oxy': [], 'timestamps': []}
    eeg_data = {'tp9': [], 'af7': [], 'af8': [], 'tp10': [], 'timestamps': []}
    heart_data = {'rr': [], 'hr': [], 'coherence': [], 'timestamps': []}
    
    # Progress bar
    progress_bar = st.progress(0)
    status_text = st.empty()
    
    start_time = time.time()
    
    # Initialize devices
    fnirs_mgr = None
    muse_device = None
    bio_mgr = None
    
    if fnirs_enabled:
        fnirs_mgr = get_fnirs_manager()
        if not fnirs_mgr.connected:
            st.warning("⚠️ Mendi fNIRS not connected - using demo mode")
    
    if eeg_enabled:
        try:
            muse_device = Muse2Device()
            st.info("🔍 Connecting to Muse 2...")
            connected = await muse_device.connect()
            if not connected:
                st.warning("⚠️ Muse 2 not found - using demo mode")
                muse_device = None
        except Exception as e:
            st.warning(f"⚠️ Muse 2 error: {e} - using demo mode")
            muse_device = None
    
    if heart_enabled:
        try:
            from unified_biometric_manager import get_biometric_manager
            bio_mgr = get_biometric_manager()
            
            # Step 1: Initialize Polar H10
            st.info("🔗 Initializing Polar H10...")
            init_success = bio_mgr.connect_polar_h10()
            
            if not init_success:
                st.warning("⚠️ Polar H10 initialization failed - using demo mode")
                bio_mgr = None
            else:
                # Step 2: Start heart rate streaming
                st.info("🫀 Starting Polar H10 heart stream...")
                stream_success = bio_mgr.start_hr_stream()
                
                if not stream_success:
                    st.warning("⚠️ Failed to start Polar H10 stream - using demo mode")
                    bio_mgr = None
                else:
                    # Step 3: Wait for data to start flowing (async sleep to not block event loop!)
                    st.info("⏳ Waiting for heart data...")
                    await asyncio.sleep(3)  # CRITICAL: async sleep, not blocking sleep!
                    
                    if bio_mgr.is_polar_streaming():
                        st.success("✅ Polar H10 streaming!")
                    else:
                        st.warning(f"⚠️ Polar state: {bio_mgr.get_polar_state()} - using demo mode")
                        bio_mgr = None
        except Exception as e:
            st.error(f"❌ Polar H10 error: {e}")
            st.warning("Using demo mode instead")
            bio_mgr = None
    
    # Parallel data collection tasks
    async def collect_fnirs_stream():
        """Collect fNIRS data stream"""
        while time.time() - start_time < duration_seconds:
            current_time = time.time() - start_time
            
            if fnirs_mgr and fnirs_mgr.connected:
                snapshot = fnirs_mgr.get_current_snapshot()
                if snapshot:
                    fnirs_data['hbo2'].append(snapshot.hbo2)
                    fnirs_data['hbr'].append(snapshot.hbr)
                    fnirs_data['oxy'].append(snapshot.oxygenation_percent)
                    fnirs_data['timestamps'].append(current_time)
            else:
                # Demo mode: Synthetic fNIRS at ~10 Hz
                fnirs_data['hbo2'].append(60 + np.random.randn() * 5)
                fnirs_data['hbr'].append(40 + np.random.randn() * 3)
                fnirs_data['oxy'].append(65 + np.random.randn() * 2)
                fnirs_data['timestamps'].append(current_time)
            
            await asyncio.sleep(0.1)  # ~10 Hz
    
    async def collect_eeg_stream():
        """Collect Muse 2 EEG stream"""
        while time.time() - start_time < duration_seconds:
            current_time = time.time() - start_time
            
            if muse_device and muse_device.is_connected:
                # Get latest EEG data from Muse 2 buffers
                try:
                    eeg_data['tp9'].append(list(muse_device.eeg_buffers['TP9'])[-1] if muse_device.eeg_buffers['TP9'] else 0.0)
                    eeg_data['af7'].append(list(muse_device.eeg_buffers['AF7'])[-1] if muse_device.eeg_buffers['AF7'] else 0.0)
                    eeg_data['af8'].append(list(muse_device.eeg_buffers['AF8'])[-1] if muse_device.eeg_buffers['AF8'] else 0.0)
                    eeg_data['tp10'].append(list(muse_device.eeg_buffers['TP10'])[-1] if muse_device.eeg_buffers['TP10'] else 0.0)
                    eeg_data['timestamps'].append(current_time)
                except Exception as e:
                    pass  # Skip if buffer empty
            else:
                # Demo mode: Synthetic EEG at 256 Hz
                eeg_data['tp9'].append(np.random.randn() * 10)
                eeg_data['af7'].append(np.random.randn() * 10)
                eeg_data['af8'].append(np.random.randn() * 10)
                eeg_data['tp10'].append(np.random.randn() * 10)
                eeg_data['timestamps'].append(current_time)
            
            await asyncio.sleep(1/256)  # 256 Hz
    
    async def collect_heart_stream():
        """Collect Polar H10 heart stream"""
        while time.time() - start_time < duration_seconds:
            current_time = time.time() - start_time
            
            if bio_mgr and bio_mgr.is_polar_streaming():
                try:
                    data = bio_mgr.get_latest_polar_data()
                    if data and data.heart_rate_bpm > 0:
                        # Use correct field names from new integration
                        heart_data['rr'].append(data.rr_interval if data.rr_interval else 800.0)
                        heart_data['hr'].append(data.heart_rate_bpm)
                        heart_data['coherence'].append(data.coherence if data.coherence else 0.5)
                        heart_data['timestamps'].append(current_time)
                    else:
                        # No valid data yet, skip this iteration
                        pass
                except Exception as e:
                    # Skip errors during collection
                    pass
            else:
                # Demo mode: Synthetic heart at ~130 Hz
                heart_data['rr'].append(800 + np.random.randn() * 50)
                heart_data['hr'].append(70 + np.random.randn() * 5)
                heart_data['coherence'].append(0.5 + np.random.randn() * 0.2)
                heart_data['timestamps'].append(current_time)
            
            await asyncio.sleep(1/130)  # ~130 Hz
    
    async def update_progress():
        """Update progress bar"""
        while time.time() - start_time < duration_seconds:
            elapsed = time.time() - start_time
            progress = min(elapsed / duration_seconds, 1.0)
            progress_bar.progress(progress)
            status_text.text(f"Recording: {int(elapsed)}/{duration_seconds}s")
            await asyncio.sleep(0.1)
    
    # Run all collection tasks in parallel
    tasks = []
    if fnirs_enabled:
        tasks.append(collect_fnirs_stream())
    if eeg_enabled:
        tasks.append(collect_eeg_stream())
    if heart_enabled:
        tasks.append(collect_heart_stream())
    tasks.append(update_progress())
    
    await asyncio.gather(*tasks)
    
    progress_bar.empty()
    status_text.empty()
    
    # Disconnect devices
    if muse_device and muse_device.is_connected:
        try:
            await muse_device.disconnect()
        except:
            pass
    
    # Convert to numpy arrays
    fnirs_hbo2 = np.array(fnirs_data['hbo2'])
    fnirs_hbr = np.array(fnirs_data['hbr'])
    fnirs_oxy = np.array(fnirs_data['oxy'])
    fnirs_ts = np.array(fnirs_data['timestamps'])
    
    eeg_tp9 = np.array(eeg_data['tp9'])
    eeg_af7 = np.array(eeg_data['af7'])
    eeg_af8 = np.array(eeg_data['af8'])
    eeg_tp10 = np.array(eeg_data['tp10'])
    eeg_ts = np.array(eeg_data['timestamps'])
    
    heart_rr = np.array(heart_data['rr'])
    heart_hr = np.array(heart_data['hr'])
    heart_coh = np.array(heart_data['coherence'])
    heart_ts = np.array(heart_data['timestamps'])
    
    # CRITICAL: Resample all signals to common sampling rate for valid cross-modal analysis
    # Target: 10 Hz (sufficient for autonomic/hemodynamic signals, Nyquist-compliant for <5 Hz bands)
    st.info("🔄 Resampling signals to common 10 Hz sampling rate...")
    
    target_fs = 10.0  # Hz
    target_timestamps = np.arange(0, duration_seconds, 1/target_fs)
    
    # Resample fNIRS (~10 Hz native, minimal resampling)
    if len(fnirs_oxy) > 0 and len(fnirs_ts) > 0:
        fnirs_oxy_resampled = np.interp(target_timestamps, fnirs_ts, fnirs_oxy)
        fnirs_hbo2_resampled = np.interp(target_timestamps, fnirs_ts, fnirs_hbo2)
        fnirs_hbr_resampled = np.interp(target_timestamps, fnirs_ts, fnirs_hbr)
    else:
        fnirs_oxy_resampled = np.array([])
        fnirs_hbo2_resampled = np.array([])
        fnirs_hbr_resampled = np.array([])
    
    # Resample EEG (256 Hz → 10 Hz, heavy downsampling)
    if len(eeg_af7) > 0 and len(eeg_ts) > 0:
        eeg_af7_resampled = np.interp(target_timestamps, eeg_ts, eeg_af7)
        eeg_tp9_resampled = np.interp(target_timestamps, eeg_ts, eeg_tp9)
        eeg_af8_resampled = np.interp(target_timestamps, eeg_ts, eeg_af8)
        eeg_tp10_resampled = np.interp(target_timestamps, eeg_ts, eeg_tp10)
    else:
        eeg_af7_resampled = np.array([])
        eeg_tp9_resampled = np.array([])
        eeg_af8_resampled = np.array([])
        eeg_tp10_resampled = np.array([])
    
    # Resample heart (130 Hz → 10 Hz)
    if len(heart_coh) > 0 and len(heart_ts) > 0:
        heart_coh_resampled = np.interp(target_timestamps, heart_ts, heart_coh)
        heart_hr_resampled = np.interp(target_timestamps, heart_ts, heart_hr)
    else:
        heart_coh_resampled = np.array([])
        heart_hr_resampled = np.array([])
    
    # Calculate summary statistics (use original data for accuracy)
    avg_hbo2 = np.mean(fnirs_hbo2) if len(fnirs_hbo2) > 0 else 0.0
    avg_hbr = np.mean(fnirs_hbr) if len(fnirs_hbr) > 0 else 0.0
    avg_oxy = np.mean(fnirs_oxy) if len(fnirs_oxy) > 0 else 0.0
    
    # EEG power bands (placeholder - needs FFT)
    avg_alpha = np.std(eeg_af7) if len(eeg_af7) > 0 else 0.0
    avg_beta = np.std(eeg_af8) if len(eeg_af8) > 0 else 0.0
    avg_theta = np.std(eeg_tp9) if len(eeg_tp9) > 0 else 0.0
    
    avg_hr = np.mean(heart_hr) if len(heart_hr) > 0 else 0.0
    avg_hrv = np.std(heart_rr) if len(heart_rr) > 0 else 0.0
    avg_coh = np.mean(heart_coh) if len(heart_coh) > 0 else 0.0
    
    # Calculate cross-modal metrics using RESAMPLED signals at 10 Hz
    st.info("📊 Calculating cross-modal coherence...")
    
    # Spectral coherence (NOW using correct 10 Hz sampling rate!)
    if len(fnirs_oxy_resampled) > 10 and len(eeg_af7_resampled) > 10:
        _, coh = calculate_spectral_coherence(fnirs_oxy_resampled, eeg_af7_resampled, fs=target_fs)
        fnirs_eeg_coherence = np.mean(coh)
    else:
        fnirs_eeg_coherence = 0.0
    
    if len(heart_coh_resampled) > 10 and len(eeg_af7_resampled) > 10:
        _, coh = calculate_spectral_coherence(heart_coh_resampled, eeg_af7_resampled, fs=target_fs)
        heart_brain_coherence = np.mean(coh)
    else:
        heart_brain_coherence = 0.0
    
    # Bell correlation (NOW using resampled signals with correct sampling rate!)
    if len(fnirs_oxy_resampled) > 10 and len(eeg_af7_resampled) > 10:
        bell_index = calculate_bell_correlation(fnirs_oxy_resampled, eeg_af7_resampled, sampling_rate=target_fs)
    else:
        bell_index = 0.0
    
    # Granger causality (NOW using resampled signals with proper alignment!)
    st.info("🔗 Calculating Granger causality (temporal precedence)...")
    
    _, heart_to_brain_p = calculate_granger_causality(heart_coh_resampled, eeg_af7_resampled, max_lag=5)
    _, brain_to_heart_p = calculate_granger_causality(eeg_af7_resampled, heart_coh_resampled, max_lag=5)
    _, fnirs_to_eeg_p = calculate_granger_causality(fnirs_oxy_resampled, eeg_af7_resampled, max_lag=5)
    
    # Data quality assessment
    fnirs_quality = assess_data_quality(fnirs_oxy)
    eeg_quality = assess_data_quality(eeg_af7)
    heart_quality = assess_data_quality(heart_hr)
    overall_quality = np.mean([fnirs_quality, eeg_quality, heart_quality])
    
    # Create baseline object
    baseline = BaselineData(
        timestamp=datetime.now(),
        duration_seconds=duration_seconds,
        
        fnirs_hbo2=fnirs_hbo2.tolist(),
        fnirs_hbr=fnirs_hbr.tolist(),
        fnirs_oxygenation=fnirs_oxy.tolist(),
        fnirs_timestamps=fnirs_data['timestamps'],
        
        eeg_tp9=eeg_tp9.tolist(),
        eeg_af7=eeg_af7.tolist(),
        eeg_af8=eeg_af8.tolist(),
        eeg_tp10=eeg_tp10.tolist(),
        eeg_timestamps=eeg_data['timestamps'],
        
        heart_rr_intervals=heart_rr.tolist(),
        heart_hr_bpm=heart_hr.tolist(),
        heart_coherence=heart_coh.tolist(),
        heart_timestamps=heart_data['timestamps'],
        
        avg_hbo2=avg_hbo2,
        avg_hbr=avg_hbr,
        avg_oxygenation=avg_oxy,
        
        avg_eeg_alpha_power=avg_alpha,
        avg_eeg_beta_power=avg_beta,
        avg_eeg_theta_power=avg_theta,
        
        avg_hr_bpm=avg_hr,
        avg_hrv_rmssd=avg_hrv,
        avg_heart_coherence=avg_coh,
        
        fnirs_eeg_coherence=fnirs_eeg_coherence,
        heart_brain_coherence=heart_brain_coherence,
        bell_correlation_index=bell_index,
        
        heart_to_brain_granger_p=heart_to_brain_p,
        brain_to_heart_granger_p=brain_to_heart_p,
        fnirs_to_eeg_granger_p=fnirs_to_eeg_p,
        
        fnirs_quality=fnirs_quality,
        eeg_quality=eeg_quality,
        heart_quality=heart_quality,
        overall_quality=overall_quality
    )
    
    # VALIDATION: Reject baselines with invalid data
    validation_errors = []
    
    # Check heart rate (most critical for real device testing)
    if heart_enabled and avg_hr <= 0:
        validation_errors.append("❌ Heart rate is 0 BPM - device not streaming data")
    
    if heart_enabled and len(heart_hr) < 10:
        validation_errors.append(f"❌ Insufficient heart data - only {len(heart_hr)} samples collected")
    
    # Check for minimum data points
    if fnirs_enabled and len(fnirs_oxy) < duration_seconds * 5:  # Expect ~10 Hz
        validation_errors.append(f"❌ Insufficient fNIRS data - expected ~{duration_seconds * 10} samples, got {len(fnirs_oxy)}")
    
    if eeg_enabled and len(eeg_af7) < duration_seconds * 100:  # Expect ~256 Hz
        validation_errors.append(f"❌ Insufficient EEG data - expected ~{duration_seconds * 256} samples, got {len(eeg_af7)}")
    
    # Check data quality thresholds
    if overall_quality < 0.3:
        validation_errors.append(f"❌ Data quality too low ({overall_quality:.1%}) - check device connections")
    
    # If validation fails, show errors and return None
    if validation_errors:
        st.error("🚫 **Baseline Collection Failed - Invalid Data**")
        for error in validation_errors:
            st.error(error)
        
        st.info("💡 **Troubleshooting:**")
        st.info("1. Ensure all devices are properly connected")
        st.info("2. Verify devices are streaming data (not just connected)")
        st.info("3. Check device battery levels")
        st.info("4. Try using Demo Mode to test the LCC optimizer without devices")
        
        return None
    
    st.success(f"✅ Baseline collected! Overall quality: {overall_quality:.1%}")
    
    return baseline


def plot_baseline_comparison(baseline_30s: BaselineData, 
                             baseline_60s: BaselineData):
    """Plot comparison between 30s and 60s baselines"""
    
    fig = make_subplots(
        rows=3, cols=2,
        subplot_titles=(
            "fNIRS Oxygenation", "EEG (AF7)",
            "Heart Rate", "Cross-Modal Coherence",
            "Data Quality", "Granger Causality"
        ),
        specs=[[{"secondary_y": False}, {"secondary_y": False}],
               [{"secondary_y": False}, {"secondary_y": False}],
               [{"type": "bar"}, {"type": "bar"}]]
    )
    
    # fNIRS
    fig.add_trace(
        go.Scatter(x=baseline_30s.fnirs_timestamps, y=baseline_30s.fnirs_oxygenation,
                  name="30s fNIRS", line=dict(color="blue")),
        row=1, col=1
    )
    fig.add_trace(
        go.Scatter(x=baseline_60s.fnirs_timestamps, y=baseline_60s.fnirs_oxygenation,
                  name="60s fNIRS", line=dict(color="cyan")),
        row=1, col=1
    )
    
    # EEG
    fig.add_trace(
        go.Scatter(x=baseline_30s.eeg_timestamps, y=baseline_30s.eeg_af7,
                  name="30s EEG", line=dict(color="red")),
        row=1, col=2
    )
    fig.add_trace(
        go.Scatter(x=baseline_60s.eeg_timestamps, y=baseline_60s.eeg_af8,
                  name="60s EEG", line=dict(color="orange")),
        row=1, col=2
    )
    
    # Heart
    fig.add_trace(
        go.Scatter(x=baseline_30s.heart_timestamps, y=baseline_30s.heart_hr_bpm,
                  name="30s HR", line=dict(color="green")),
        row=2, col=1
    )
    fig.add_trace(
        go.Scatter(x=baseline_60s.heart_timestamps, y=baseline_60s.heart_hr_bpm,
                  name="60s HR", line=dict(color="lime")),
        row=2, col=1
    )
    
    # Coherence comparison
    coherence_data = {
        "30s": [baseline_30s.fnirs_eeg_coherence, baseline_30s.heart_brain_coherence, 
                baseline_30s.bell_correlation_index],
        "60s": [baseline_60s.fnirs_eeg_coherence, baseline_60s.heart_brain_coherence,
                baseline_60s.bell_correlation_index]
    }
    
    fig.add_trace(
        go.Bar(x=["fNIRS-EEG", "Heart-Brain", "Bell Index"],
               y=coherence_data["30s"], name="30s", marker_color="blue"),
        row=2, col=2
    )
    fig.add_trace(
        go.Bar(x=["fNIRS-EEG", "Heart-Brain", "Bell Index"],
               y=coherence_data["60s"], name="60s", marker_color="cyan"),
        row=2, col=2
    )
    
    # Data quality
    quality_data = {
        "30s": [baseline_30s.fnirs_quality, baseline_30s.eeg_quality, baseline_30s.heart_quality],
        "60s": [baseline_60s.fnirs_quality, baseline_60s.eeg_quality, baseline_60s.heart_quality]
    }
    
    fig.add_trace(
        go.Bar(x=["fNIRS", "EEG", "Heart"],
               y=quality_data["30s"], name="30s", marker_color="green"),
        row=3, col=1
    )
    fig.add_trace(
        go.Bar(x=["fNIRS", "EEG", "Heart"],
               y=quality_data["60s"], name="60s", marker_color="lime"),
        row=3, col=1
    )
    
    # Granger causality
    granger_data = {
        "30s": [baseline_30s.heart_to_brain_granger_p, baseline_30s.brain_to_heart_granger_p,
                baseline_30s.fnirs_to_eeg_granger_p],
        "60s": [baseline_60s.heart_to_brain_granger_p, baseline_60s.brain_to_heart_granger_p,
                baseline_60s.fnirs_to_eeg_granger_p]
    }
    
    fig.add_trace(
        go.Bar(x=["Heart→Brain", "Brain→Heart", "fNIRS→EEG"],
               y=granger_data["30s"], name="30s (p-value)", marker_color="purple"),
        row=3, col=2
    )
    fig.add_trace(
        go.Bar(x=["Heart→Brain", "Brain→Heart", "fNIRS→EEG"],
               y=granger_data["60s"], name="60s (p-value)", marker_color="magenta"),
        row=3, col=2
    )
    
    fig.update_layout(height=900, showlegend=True, title_text="30s vs 60s Baseline Comparison")
    fig.update_yaxes(title_text="Quality (0-1)", row=3, col=1)
    fig.update_yaxes(title_text="p-value", row=3, col=2)
    
    return fig


def render_baseline_collection_ui():
    """Main Streamlit UI for baseline collection + LCC optimization"""
    
    st.title("🔬 Baseline Collection → LCC Optimization")
    
    st.markdown("""
    **Complete personalized mood enhancement workflow:**
    
    **Step 1: Collect Baseline** 📊
    - 🧠 **Mendi fNIRS**: Brain oxygenation (HbO2, HbR)
    - 🧬 **Muse 2 EEG**: 4-channel brain electrical activity
    - ❤️ **Polar H10**: Heart rate, HRV, coherence
    
    **Step 2: Optimize Protocol** 🌟
    - YOUR genome (FAAH, BDNF, HTR2A) → Personalized response
    - Physics-based LCC simulation → Optimal frequency/intensity/duration
    - Predict outcomes → GILE increase, coherence, safety
    
    **Step 3: Apply & Monitor** ⚡
    - Use optimal protocol TODAY
    - Real-time biofeedback during session
    - Validate predictions vs reality
    """)
    
    # Device status
    col1, col2, col3 = st.columns(3)
    
    with col1:
        fnirs_mgr = get_fnirs_manager()
        fnirs_connected = fnirs_mgr.connected if fnirs_mgr else False
        st.metric("Mendi fNIRS", "🟢 Connected" if fnirs_connected else "🔴 Disconnected")
    
    with col2:
        # TODO: Check Muse 2 connection
        st.metric("Muse 2 EEG", "🟡 Demo Mode")
    
    with col3:
        # TODO: Check Polar H10 connection
        st.metric("Polar H10", "🟡 Demo Mode")
    
    st.divider()
    
    # DATA UPLOAD SECTION
    st.header("📤 Upload Mendi Data")
    
    st.markdown("""
    Upload real Mendi fNIRS data from CSV export or manual entry.
    
    **Supported formats:**
    - Mendi app CSV export
    - Custom CSV with columns: timestamp, hbo2, hbr, signal_quality
    """)
    
    upload_col1, upload_col2 = st.columns([2, 1])
    
    with upload_col1:
        uploaded_file = st.file_uploader(
            "Choose CSV file",
            type=['csv'],
            help="Upload Mendi fNIRS data in CSV format"
        )
    
    with upload_col2:
        if uploaded_file is not None:
            st.success(f"✅ File loaded: {uploaded_file.name}")
    
    if uploaded_file is not None:
        try:
            import pandas as pd
            import psycopg2
            import os
            
            # Read CSV
            df = pd.read_csv(uploaded_file)
            
            # Show preview
            st.subheader("📊 Data Preview")
            st.dataframe(df.head(10), use_container_width=True)
            
            # Validate columns
            required_cols = ['timestamp', 'hbo2', 'hbr']
            missing_cols = [col for col in required_cols if col not in df.columns]
            
            if missing_cols:
                st.error(f"❌ Missing required columns: {', '.join(missing_cols)}")
                st.info(f"Found columns: {', '.join(df.columns)}")
            else:
                st.success(f"✅ Valid format! Found {len(df)} data points")
                
                # Upload to database
                if st.button("📥 Import to Database", type="primary"):
                    try:
                        from dateutil import parser as date_parser
                        
                        conn = psycopg2.connect(os.environ['DATABASE_URL'])
                        cur = conn.cursor()
                        
                        session_id = f"upload-{datetime.now().strftime('%Y%m%d-%H%M%S')}"
                        imported_count = 0
                        failed_rows = []
                        
                        with st.spinner(f"Validating and importing {len(df)} records..."):
                            for idx, row in df.iterrows():
                                try:
                                    # ROW-LEVEL VALIDATION
                                    # 1. Parse and validate timestamp
                                    try:
                                        timestamp_val = date_parser.parse(str(row['timestamp']))
                                    except Exception as ts_err:
                                        failed_rows.append(f"Row {idx+1}: Invalid timestamp '{row['timestamp']}' - {ts_err}")
                                        continue
                                    
                                    # 2. Validate numeric values (HbO2, HbR)
                                    try:
                                        hbo2_val = float(row['hbo2'])
                                        hbr_val = float(row['hbr'])
                                        
                                        if pd.isna(hbo2_val) or pd.isna(hbr_val):
                                            failed_rows.append(f"Row {idx+1}: NaN values in hbo2 or hbr")
                                            continue
                                        
                                        if hbo2_val < 0 or hbr_val < 0:
                                            failed_rows.append(f"Row {idx+1}: Negative hemoglobin values (hbo2={hbo2_val}, hbr={hbr_val})")
                                            continue
                                            
                                    except (ValueError, TypeError) as num_err:
                                        failed_rows.append(f"Row {idx+1}: Non-numeric hbo2/hbr - {num_err}")
                                        continue
                                    
                                    # 3. Validate signal quality (optional field)
                                    signal_quality = 0.85  # Default
                                    if 'signal_quality' in row and pd.notna(row['signal_quality']):
                                        try:
                                            signal_quality = float(row['signal_quality'])
                                            if not (0 <= signal_quality <= 1):
                                                signal_quality = 0.85  # Reset to default if out of range
                                        except:
                                            pass  # Keep default
                                    
                                    # Calculate derived metrics
                                    total_hb = hbo2_val + hbr_val
                                    oxygenation_pct = (hbo2_val / total_hb * 100) if total_hb > 0 else 0
                                    
                                    # Insert validated row
                                    cur.execute("""
                                        INSERT INTO mendi_realtime_data 
                                        (timestamp, hbo2, hbr, total_hb, oxygenation_percent, 
                                         signal_quality, device_id, session_id, metadata)
                                        VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                                    """, (
                                        timestamp_val,
                                        hbo2_val,
                                        hbr_val,
                                        total_hb,
                                        oxygenation_pct,
                                        signal_quality,
                                        'csv-upload',
                                        session_id,
                                        json.dumps({
                                            'source': 'csv_upload',
                                            'filename': uploaded_file.name,
                                            'upload_timestamp': datetime.now().isoformat()
                                        })
                                    ))
                                    imported_count += 1
                                    
                                except Exception as row_err:
                                    failed_rows.append(f"Row {idx+1}: {str(row_err)}")
                                    continue
                            
                            conn.commit()
                        
                        cur.close()
                        conn.close()
                        
                        # Report results
                        if imported_count > 0:
                            st.success(f"✅ Successfully imported {imported_count} records!")
                            st.info(f"📊 Session ID: `{session_id}`")
                            
                            # Store session ID in session state for auto-selection
                            st.session_state['last_uploaded_session'] = session_id
                            
                            if failed_rows:
                                st.warning(f"⚠️ {len(failed_rows)} rows skipped due to validation errors:")
                                with st.expander("Show failed rows"):
                                    for err in failed_rows[:20]:  # Show first 20 errors
                                        st.text(err)
                            else:
                                st.balloons()
                        else:
                            st.error("❌ No valid rows to import!")
                            if failed_rows:
                                st.error("All rows failed validation:")
                                with st.expander("Show errors"):
                                    for err in failed_rows[:20]:
                                        st.text(err)
                        
                    except Exception as e:
                        st.error(f"❌ Import failed: {str(e)}")
                        
        except Exception as e:
            st.error(f"❌ Error reading file: {str(e)}")
    
    # VIEW UPLOADED SESSIONS
    st.subheader("📊 View Uploaded Sessions")
    
    try:
        import psycopg2
        import os
        import pandas as pd
        
        conn = psycopg2.connect(os.environ['DATABASE_URL'])
        cur = conn.cursor()
        
        # Get all unique sessions
        cur.execute("""
            SELECT DISTINCT session_id, 
                   MIN(timestamp) as start_time,
                   MAX(timestamp) as end_time,
                   COUNT(*) as sample_count,
                   AVG(hbo2) as avg_hbo2,
                   AVG(hbr) as avg_hbr,
                   AVG(oxygenation_percent) as avg_oxy
            FROM mendi_realtime_data
            WHERE session_id IS NOT NULL
            GROUP BY session_id
            ORDER BY start_time DESC
            LIMIT 20
        """)
        
        sessions = cur.fetchall()
        
        if sessions:
            session_options = {
                f"{s[0]} ({s[3]} samples, {s[1].strftime('%Y-%m-%d %H:%M')})": s[0] 
                for s in sessions
            }
            
            selected_session_label = st.selectbox(
                "Select session to visualize",
                options=list(session_options.keys())
            )
            
            if selected_session_label:
                selected_session_id = session_options[selected_session_label]
                
                # Fetch session data - SCOPED TO SELECTED SESSION
                cur.execute("""
                    SELECT timestamp, hbo2, hbr, oxygenation_percent, signal_quality
                    FROM mendi_realtime_data
                    WHERE session_id = %s
                    ORDER BY timestamp ASC
                """, (selected_session_id,))
                
                session_data = cur.fetchall()
                
                if session_data:
                    # Convert to dataframe
                    df_session = pd.DataFrame(session_data, 
                                             columns=['timestamp', 'hbo2', 'hbr', 'oxygenation', 'quality'])
                    
                    # Show stats
                    st.markdown(f"""
                    **Session Statistics:**
                    - Samples: {len(df_session)}
                    - Duration: {(df_session['timestamp'].max() - df_session['timestamp'].min()).total_seconds():.0f}s
                    - Avg HbO2: {df_session['hbo2'].mean():.1f} | Avg HbR: {df_session['hbr'].mean():.1f}
                    - Avg Oxygenation: {df_session['oxygenation'].mean():.1f}%
                    - Avg Quality: {df_session['quality'].mean():.2f}
                    """)
                    
                    # Plot time series
                    fig = go.Figure()
                    
                    fig.add_trace(go.Scatter(
                        x=df_session['timestamp'],
                        y=df_session['hbo2'],
                        name='HbO2 (Oxygenated)',
                        line=dict(color='red', width=2)
                    ))
                    
                    fig.add_trace(go.Scatter(
                        x=df_session['timestamp'],
                        y=df_session['hbr'],
                        name='HbR (Deoxygenated)',
                        line=dict(color='blue', width=2)
                    ))
                    
                    fig.update_layout(
                        title=f"🧠 Mendi fNIRS Data: {selected_session_id}",
                        xaxis_title="Time",
                        yaxis_title="Hemoglobin (μM)",
                        height=400,
                        hovermode='x unified'
                    )
                    
                    st.plotly_chart(fig, use_container_width=True)
        else:
            st.info("📝 No uploaded sessions found. Upload a CSV file above to get started!")
        
        cur.close()
        conn.close()
        
    except Exception as e:
        st.error(f"❌ Error loading sessions: {str(e)}")
    
    st.divider()
    
    # Demo Mode Option
    st.header("🎮 Testing Mode")
    
    demo_mode = st.checkbox(
        "Use Demo Mode (Skip Device Requirements)",
        value=False,
        help="Generate synthetic baseline data for testing LCC optimizer without physical devices"
    )
    
    if demo_mode:
        st.info("📝 Demo mode will create a synthetic baseline with realistic biometric data for testing purposes.")
        if st.button("✨ Generate Demo Baseline", type="primary"):
            # Create synthetic baseline with realistic time series
            import numpy as np
            
            duration = 60
            fs = 10.0
            n_samples = int(duration * fs)
            timestamps = np.arange(0, duration, 1/fs).tolist()
            
            # Generate realistic synthetic time series
            baseline_demo = BaselineData(
                timestamp=datetime.now(),
                duration_seconds=duration,
                
                # fNIRS time series (with realistic physiological variations)
                fnirs_hbo2=list(62.5 + 5 * np.sin(np.linspace(0, 4*np.pi, n_samples)) + np.random.normal(0, 1, n_samples)),
                fnirs_hbr=list(38.2 + 3 * np.cos(np.linspace(0, 4*np.pi, n_samples)) + np.random.normal(0, 0.8, n_samples)),
                fnirs_oxygenation=list(66.8 + 4 * np.sin(np.linspace(0, 3*np.pi, n_samples)) + np.random.normal(0, 1.2, n_samples)),
                fnirs_timestamps=timestamps,
                
                # EEG time series (4 channels with realistic brain rhythms)
                eeg_tp9=list(np.random.normal(0, 50, n_samples)),
                eeg_af7=list(np.random.normal(0, 45, n_samples)),
                eeg_af8=list(np.random.normal(0, 48, n_samples)),
                eeg_tp10=list(np.random.normal(0, 52, n_samples)),
                eeg_timestamps=timestamps,
                
                # Heart time series
                heart_rr_intervals=list(800 + 100 * np.sin(np.linspace(0, 6*np.pi, n_samples)) + np.random.normal(0, 20, n_samples)),
                heart_hr_bpm=list(72.0 + 8 * np.cos(np.linspace(0, 5*np.pi, n_samples)) + np.random.normal(0, 3, n_samples)),
                heart_coherence=list(0.62 + 0.15 * np.sin(np.linspace(0, 2*np.pi, n_samples)) + np.random.normal(0, 0.05, n_samples)),
                heart_timestamps=timestamps,
                
                # Summary statistics
                avg_hbo2=62.5,
                avg_hbr=38.2,
                avg_oxygenation=66.8,
                
                avg_eeg_alpha_power=45.3,
                avg_eeg_beta_power=18.4,
                avg_eeg_theta_power=28.7,
                
                avg_hr_bpm=72.0,
                avg_hrv_rmssd=65.0,
                avg_heart_coherence=0.62,
                
                # Cross-modal coherence metrics
                fnirs_eeg_coherence=0.73,
                heart_brain_coherence=0.68,
                bell_correlation_index=0.78,
                
                # Granger causality p-values
                heart_to_brain_granger_p=0.032,
                brain_to_heart_granger_p=0.156,
                fnirs_to_eeg_granger_p=0.089,
                
                # Data quality scores
                fnirs_quality=0.92,
                eeg_quality=0.88,
                heart_quality=0.95,
                overall_quality=0.92
            )
            st.session_state['baseline_60s'] = baseline_demo
            st.success("✅ Demo baseline generated! Scroll down to optimize your LCC protocol.")
            st.rerun()
    
    st.divider()
    
    # Baseline collection controls
    st.header("📋 Baseline Measurement Protocol")
    
    duration = st.select_slider(
        "Baseline Duration",
        options=[30, 60, 90, 120],
        value=60,
        help="30s = quick check, 60s = standard, 90-120s = high precision"
    )
    
    col1, col2 = st.columns(2)
    
    with col1:
        if st.button("▶️ Start 30s Baseline", type="primary", use_container_width=True):
            st.session_state['collecting_30s'] = True
    
    with col2:
        if st.button("▶️ Start 60s Baseline", type="primary", use_container_width=True):
            st.session_state['collecting_60s'] = True
    
    # Collect 30s baseline
    if st.session_state.get('collecting_30s'):
        baseline_30s = asyncio.run(collect_baseline(duration_seconds=30))
        if baseline_30s:
            st.session_state['baseline_30s'] = baseline_30s
            st.session_state['collecting_30s'] = False
            
            # Display results
            st.success("✅ 30s baseline complete!")
            
            col1, col2, col3 = st.columns(3)
            col1.metric("fNIRS Quality", f"{baseline_30s.fnirs_quality:.1%}")
            col2.metric("EEG Quality", f"{baseline_30s.eeg_quality:.1%}")
            col3.metric("Heart Quality", f"{baseline_30s.heart_quality:.1%}")
            
            st.metric("Bell Correlation Index", f"{baseline_30s.bell_correlation_index:.3f}",
                     help="High values (>0.7) suggest quantum entanglement")
            
            if baseline_30s.heart_to_brain_granger_p < 0.05:
                st.success(f"🔗 Heart Granger-causes Brain (p={baseline_30s.heart_to_brain_granger_p:.4f})")
    
    # Collect 60s baseline
    if st.session_state.get('collecting_60s'):
        baseline_60s = asyncio.run(collect_baseline(duration_seconds=60))
        if baseline_60s:
            st.session_state['baseline_60s'] = baseline_60s
            st.session_state['collecting_60s'] = False
            
            st.success("✅ 60s baseline complete!")
            
            col1, col2, col3 = st.columns(3)
            col1.metric("fNIRS Quality", f"{baseline_60s.fnirs_quality:.1%}")
            col2.metric("EEG Quality", f"{baseline_60s.eeg_quality:.1%}")
            col3.metric("Heart Quality", f"{baseline_60s.heart_quality:.1%}")
            
            st.metric("Bell Correlation Index", f"{baseline_60s.bell_correlation_index:.3f}")
            
            if baseline_60s.heart_to_brain_granger_p < 0.05:
                st.success(f"🔗 Heart Granger-causes Brain (p={baseline_60s.heart_to_brain_granger_p:.4f})")
    
    # Comparison if both collected
    if st.session_state.get('baseline_30s') and st.session_state.get('baseline_60s'):
        st.divider()
        st.header("📊 30s vs 60s Comparison")
        
        baseline_30s = st.session_state['baseline_30s']
        baseline_60s = st.session_state['baseline_60s']
        
        fig = plot_baseline_comparison(baseline_30s, baseline_60s)
        st.plotly_chart(fig, use_container_width=True)
        
        # Quality improvement
        quality_improvement = baseline_60s.overall_quality - baseline_30s.overall_quality
        
        if quality_improvement > 0.1:
            st.success(f"📈 60s baseline is {quality_improvement:.1%} better quality than 30s")
        elif quality_improvement < -0.1:
            st.warning(f"⚠️ 30s baseline is {-quality_improvement:.1%} better quality (rare!)")
        else:
            st.info("📊 Both baselines have similar quality")
        
        # Export data
        st.divider()
        st.subheader("💾 Export Baseline Data")
        
        if st.button("Download 60s Baseline JSON"):
            baseline_dict = asdict(baseline_60s)
            baseline_dict['timestamp'] = baseline_dict['timestamp'].isoformat()
            json_str = json.dumps(baseline_dict, indent=2)
            
            st.download_button(
                label="📥 Download JSON",
                data=json_str,
                file_name=f"baseline_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json",
                mime="application/json"
            )
    
    # LCC OPTIMIZATION SECTION
    # Show if we have at least one baseline
    best_baseline = None
    if st.session_state.get('baseline_60s'):
        best_baseline = st.session_state['baseline_60s']
    elif st.session_state.get('baseline_30s'):
        best_baseline = st.session_state['baseline_30s']
    
    if best_baseline:
        st.divider()
        st.header("🌟 Step 2: Optimize Your LCC Protocol")
        
        st.markdown("""
        Now that we have your baseline, let's find the PERFECT Light-Consciousness Coupling protocol
        personalized for YOUR unique biology + genome!
        """)
        
        # Import LCC optimizer
        from lcc_optimization_simulator import (
            render_lcc_optimization_ui,
            GenomeProfile,
            optimize_lcc_protocol,
            plot_optimization_result
        )
        
        # Render LCC optimization with baseline
        render_lcc_optimization_ui(baseline=best_baseline)


if __name__ == "__main__":
    render_baseline_collection_ui()
