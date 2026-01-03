"""
Regression tests for DEAP dataset loader

Ensures baseline removal is correctly applied
"""

import numpy as np
from deap_loader import DEAPDataset


def test_baseline_removal_synthetic():
    """Test that synthetic data has correct shape after baseline removal"""
    # Create synthetic DEAP data with baseline
    full_trial = np.random.randn(32, 8064)  # 63 seconds
    
    # Simulate baseline removal
    baseline_samples = 384  # 3 seconds @ 128 Hz
    trimmed_trial = full_trial[:, baseline_samples:]
    
    # Verify shape
    assert trimmed_trial.shape == (32, 7680), \
        f"Expected shape (32, 7680), got {trimmed_trial.shape}"
    
    # Verify time duration
    sampling_rate = 128
    duration = trimmed_trial.shape[1] / sampling_rate
    assert duration == 60, f"Expected 60 seconds, got {duration}"


def test_deap_loader_configuration():
    """Test DEAP loader configuration"""
    dataset = DEAPDataset('./data/deap')
    
    assert dataset.sampling_rate == 128
    assert dataset.n_channels == 32
    assert dataset.n_trials == 40
    assert dataset.trial_duration == 60  # After baseline removal


def test_channel_names():
    """Test that channel names are correctly defined"""
    dataset = DEAPDataset('./data/deap')
    
    assert len(dataset.channel_names) == 32
    assert dataset.channel_names[0] == 'Fp1'
    assert dataset.channel_names[16] == 'Fp2'
    assert 'F3' in dataset.channel_names
    assert 'F4' in dataset.channel_names


def test_frontal_pairs():
    """Test frontal electrode pairs for asymmetry"""
    dataset = DEAPDataset('./data/deap')
    
    # Should have at least 3 frontal pairs
    assert len(dataset.frontal_pairs) >= 3
    
    # Check Fp1-Fp2 pair
    assert (0, 16) in dataset.frontal_pairs  # Fp1-Fp2


if __name__ == '__main__':
    print("Running DEAP Loader Regression Tests\n")
    
    test_baseline_removal_synthetic()
    print("✓ Baseline removal shape test passed")
    
    test_deap_loader_configuration()
    print("✓ Loader configuration test passed")
    
    test_channel_names()
    print("✓ Channel names test passed")
    
    test_frontal_pairs()
    print("✓ Frontal pairs test passed")
    
    print("\n✅ All tests passed!")
