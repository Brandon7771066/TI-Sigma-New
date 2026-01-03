"""
DEAP Dataset Loader and Utilities

The DEAP (Database for Emotion Analysis using Physiological signals) dataset
contains EEG recordings from 32 participants watching 40 music videos.

Dataset Structure:
- 32 participants (s01.dat to s32.dat)
- 40 trials per participant (one-minute music videos)
- 32 EEG channels + 8 peripheral channels (total 40 channels)
- Labels: valence, arousal, dominance, liking (1-9 scale)

Download Instructions:
1. Visit: http://www.eecs.qmul.ac.uk/mmv/datasets/deap/
2. Sign agreement and download preprocessed Python pickle files
3. Place .dat files in ./data/deap/ directory
4. Files: s01.dat, s02.dat, ..., s32.dat

File format:
Each .dat file contains:
- data: (40 trials, 40 channels, 8064 timepoints) at 128 Hz
  - Channels 0-31: EEG
  - Channels 32-39: Peripheral (EOG, EMG, GSR, etc.)
- labels: (40 trials, 4 values)
  - Column 0: Valence (1-9)
  - Column 1: Arousal (1-9)
  - Column 2: Dominance (1-9)
  - Column 3: Liking (1-9)
"""

import pickle
import numpy as np
from pathlib import Path
from typing import Tuple, Optional, List
import warnings

class DEAPDataset:
    """
    DEAP Dataset Loader
    
    Usage:
        dataset = DEAPDataset('./data/deap')
        eeg, labels = dataset.load_participant(1)
        
        # Get single trial
        trial_eeg = eeg[0]  # First trial, shape (32, 8064)
        trial_valence = labels[0, 0]  # 1-9 scale
        trial_arousal = labels[0, 1]
    """
    
    def __init__(self, data_dir: str = './data/deap'):
        self.data_dir = Path(data_dir)
        self.sampling_rate = 128  # Hz
        self.n_channels = 32  # EEG channels
        self.n_trials = 40
        self.trial_duration = 60  # seconds after removing 3s baseline (7680 / 128)
        
        # Channel names (10-20 system)
        self.channel_names = [
            'Fp1', 'AF3', 'F3', 'F7', 'FC5', 'FC1', 'C3', 'T7',
            'CP5', 'CP1', 'P3', 'P7', 'PO3', 'O1', 'Oz', 'Pz',
            'Fp2', 'AF4', 'Fz', 'F4', 'F8', 'FC6', 'FC2', 'Cz',
            'C4', 'T8', 'CP6', 'CP2', 'P4', 'P8', 'PO4', 'O2'
        ]
        
        # Channel pairs for asymmetry analysis
        self.frontal_pairs = [
            (0, 16),   # Fp1-Fp2
            (2, 19),   # F3-F4
            (3, 20),   # F7-F8
        ]
        
        if not self.data_dir.exists():
            warnings.warn(
                f"DEAP data directory not found: {self.data_dir}\n"
                f"Please download DEAP dataset from:\n"
                f"http://www.eecs.qmul.ac.uk/mmv/datasets/deap/\n"
                f"and place .dat files in {self.data_dir}"
            )
    
    def load_participant(self, participant_id: int) -> Tuple[np.ndarray, np.ndarray]:
        """
        Load data for a single participant
        
        Args:
            participant_id: 1-32
            
        Returns:
            eeg: (40 trials, 32 channels, 7680 timepoints) - baseline removed
            labels: (40 trials, 4) - valence, arousal, dominance, liking
            
        Note: First 3 seconds (384 samples) baseline period is automatically removed
        """
        if not 1 <= participant_id <= 32:
            raise ValueError(f"Participant ID must be 1-32, got {participant_id}")
        
        filename = self.data_dir / f's{participant_id:02d}.dat'
        
        if not filename.exists():
            raise FileNotFoundError(
                f"File not found: {filename}\n"
                f"Download DEAP dataset and place in {self.data_dir}"
            )
        
        with open(filename, 'rb') as f:
            data = pickle.load(f, encoding='latin1')
        
        # Extract EEG channels (first 32 channels)
        # Remove baseline (first 3 seconds = 384 samples @ 128 Hz)
        # DEAP trials: 3s baseline + 60s stimulus = 63s total = 8064 samples
        baseline_samples = 384  # 3 seconds * 128 Hz
        eeg = data['data'][:, :32, baseline_samples:]  # Skip baseline
        labels = data['labels']
        
        return eeg, labels
    
    def load_all_participants(self) -> Tuple[List[np.ndarray], List[np.ndarray]]:
        """
        Load all available participants
        
        Returns:
            eeg_list: List of EEG arrays, one per participant
            labels_list: List of label arrays, one per participant
        """
        eeg_list = []
        labels_list = []
        
        for participant_id in range(1, 33):
            try:
                eeg, labels = self.load_participant(participant_id)
                eeg_list.append(eeg)
                labels_list.append(labels)
                print(f"✓ Loaded participant {participant_id}")
            except FileNotFoundError:
                print(f"✗ Skipped participant {participant_id} (file not found)")
        
        return eeg_list, labels_list
    
    def get_trial_segment(
        self, 
        eeg: np.ndarray, 
        start_time: float = 0, 
        duration: float = 10
    ) -> np.ndarray:
        """
        Extract a time segment from a trial
        
        Args:
            eeg: (32 channels, 8064 timepoints) or (n_trials, 32, 8064)
            start_time: Start time in seconds
            duration: Duration in seconds
            
        Returns:
            segment: EEG segment
        """
        start_sample = int(start_time * self.sampling_rate)
        end_sample = int((start_time + duration) * self.sampling_rate)
        
        if eeg.ndim == 2:
            return eeg[:, start_sample:end_sample]
        else:
            return eeg[:, :, start_sample:end_sample]
    
    def binary_labels(
        self, 
        labels: np.ndarray, 
        dimension: int = 0, 
        threshold: float = 5.0
    ) -> np.ndarray:
        """
        Convert continuous labels to binary (high/low)
        
        Args:
            labels: (n_trials, 4) array
            dimension: 0=valence, 1=arousal, 2=dominance, 3=liking
            threshold: Split threshold (typically 5.0 for 1-9 scale)
            
        Returns:
            binary: 1 for high, 0 for low
        """
        return (labels[:, dimension] >= threshold).astype(int)
    
    def quadrant_labels(self, labels: np.ndarray, threshold: float = 5.0) -> np.ndarray:
        """
        Convert to 4-quadrant labels (valence-arousal space)
        
        Returns:
            quadrants: 0=LALV, 1=LAHV, 2=HALV, 3=HAHV
            - 0: Low Arousal, Low Valence (Sad)
            - 1: Low Arousal, High Valence (Calm)
            - 2: High Arousal, Low Valence (Angry)
            - 3: High Arousal, High Valence (Happy)
        """
        valence_high = labels[:, 0] >= threshold
        arousal_high = labels[:, 1] >= threshold
        
        quadrants = np.zeros(len(labels), dtype=int)
        quadrants[~arousal_high & ~valence_high] = 0  # LALV
        quadrants[~arousal_high & valence_high] = 1   # LAHV
        quadrants[arousal_high & ~valence_high] = 2   # HALV
        quadrants[arousal_high & valence_high] = 3    # HAHV
        
        return quadrants


def download_instructions():
    """Print detailed download instructions for DEAP dataset"""
    
    instructions = """
╔══════════════════════════════════════════════════════════════════════════╗
║                    DEAP Dataset Download Instructions                    ║
╚══════════════════════════════════════════════════════════════════════════╝

DEAP (Database for Emotion Analysis using Physiological signals) contains:
- 32 participants watching 40 music videos each
- 32-channel EEG recorded at 128 Hz
- Valence, Arousal, Dominance, Liking ratings (1-9 scale)

DOWNLOAD STEPS:

1. Visit the official website:
   🔗 http://www.eecs.qmul.ac.uk/mmv/datasets/deap/

2. Click on "Download" in the navigation menu

3. Fill out the End User License Agreement form:
   - Provide your name, email, affiliation
   - Agree to use dataset for research only
   - Agree to cite the original paper

4. You will receive download links via email

5. Download the preprocessed Python pickle files:
   ✓ Recommended: "Preprocessed data (Python format)" (~1.8 GB)
   - This includes filtered, downsampled data ready to use
   - File: data_preprocessed_python.zip
   
   OR
   
   ✓ Alternative: "Original BDF files" (~22 GB)
   - Raw unprocessed data
   - Requires additional preprocessing

6. Extract the files:
   ```bash
   unzip data_preprocessed_python.zip
   ```

7. Create data directory structure:
   ```bash
   mkdir -p ./data/deap
   mv data_preprocessed_python/*.dat ./data/deap/
   ```

8. Verify files:
   - You should have s01.dat through s32.dat
   - Each file ~56 MB

ALTERNATIVE: Sample Synthetic Data

If you want to test the code without downloading DEAP, you can generate
synthetic data that mimics the structure:

```python
from deap_loader import DEAPDataset
import numpy as np
from pathlib import Path

# Create synthetic data
def create_synthetic_deap():
    data_dir = Path('./data/deap')
    data_dir.mkdir(parents=True, exist_ok=True)
    
    for participant_id in range(1, 6):  # Just 5 participants
        # Generate random EEG-like data
        eeg = np.random.randn(40, 32, 8064) * 10  # 40 trials
        
        # Generate random labels (1-9 scale)
        labels = np.random.uniform(1, 9, size=(40, 4))
        
        data = {
            'data': np.concatenate([
                eeg, 
                np.random.randn(40, 8, 8064)  # Peripheral channels
            ], axis=1),
            'labels': labels
        }
        
        filename = data_dir / f's{participant_id:02d}.dat'
        with open(filename, 'wb') as f:
            pickle.dump(data, f)
    
    print("✓ Created 5 synthetic participants")

create_synthetic_deap()
```

CITATION:

If you use DEAP dataset, please cite:

    S. Koelstra, C. Muhl, M. Soleymani, J.S. Lee, A. Yazdani, T. Ebrahimi, 
    T. Pun, A. Nijholt, I. Patras, "DEAP: A Database for Emotion Analysis 
    using Physiological Signals", IEEE Transactions on Affective Computing, 
    vol. 3, no. 1, pp. 18-31, January-March 2012.

═══════════════════════════════════════════════════════════════════════════
"""
    
    print(instructions)


if __name__ == '__main__':
    download_instructions()
    
    # Try to load data if available
    dataset = DEAPDataset('./data/deap')
    
    try:
        eeg, labels = dataset.load_participant(1)
        print(f"\n✓ Successfully loaded participant 1")
        print(f"  EEG shape: {eeg.shape}")
        print(f"  Labels shape: {labels.shape}")
        print(f"  Valence range: {labels[:, 0].min():.1f} - {labels[:, 0].max():.1f}")
        print(f"  Arousal range: {labels[:, 1].min():.1f} - {labels[:, 1].max():.1f}")
    except FileNotFoundError:
        print("\n⚠ DEAP data not found. Follow instructions above to download.")
