# Behavioural and EEG data from an EEG hyperscanning study examining cognitive and neural signals underlying the sense of joint agency during a musical joint action task

---

# Dataset Structure

The primary folder includes a separate folder for each pair:sub-##

Each pair folder contains:

## Behavioural Data
Located in:sub-##/beh/
File:sub-##_task-jointaction_beh.tsv

## EEG Data
Located in:sub-##/eeg/
Files (BrainVision format):
sub-##_task-jointaction_eeg.eeg
sub-##_task-jointaction_eeg.vhdr
sub-##_task-jointaction_eeg.vmrk

---

# Derivatives Folder

The `derivatives/` folder contains:

- `behavioural_all.tsv`  
  Compiled behavioural data across all pairs.

- `32chanElectrodePositions.elp`  
  Electrode positions used for EEG data acquisition and analysis.

---

# Behavioural Data Description

The following column descriptions apply to both:

- `behavioural_all.tsv`
- `sub-##_task-jointaction_beh.tsv`

---

## Pair Number
Values: 1–32

---

## Participant Number

- The first one or two digits represent the pair number.
- The last digit represents seating position:
  - `1` = left participant
  - `2` = right participant

Examples:
- `11` = left participant in pair 1
- `202` = right participant in pair 20

---

## Block Number

Test block number for a given trial (1–8).

---

## Trial Number

Each pair performed:

- 8 tone sequences  
  - 4 musical duets  
  - 4 constant pitch sequences  
- 5 joint trials per sequence  

Total:
- 40 test trials per pair  
- Trial numbers range from 1–40

---

## Experimental Condition

- `0` = constant pitch sequences  
- `1` = musical duets  

---

## Part Performed

Indicates which part of the tone sequence the participant performed:

- `0` = higher-pitch part (for constant pitch sequences) or melody part (for musical duets)
- `1` = lower-pitch part (for constant pitch sequences) or accompaniment part (for musical duets)

---

## Tone Sequence

1. Twinkle Twinkle Little Star  
2. Hush Little Baby  
3. B.I.N.G.O.  
4. Yankee Doodle  
5. Constant pitch sequence with A4 as higher-pitch part  
6. Constant pitch sequence with C5 as higher-pitch part  
7. Constant pitch sequence with E♭5 as higher-pitch part  
8. Constant pitch sequence with F♯5 as higher-pitch part  

---

## Joint Agency Ratings

Self-reported rating scale: 1–7

---

## Mean Synchronization Performance

The mean synchronization performance for each trial was calculated as follows. First, we calculated the absolute asynchrony between the two participants’ note onsets at each beat. Then, we converted each asynchrony to a proportion of the inter-onset interval (IOI) from the preceding note onset to the current note onset, which we averaged across the two participants and across all beats in the sequence.

---

## Standard Deviation (SD) of Synchronization Performance

The SD of synchronization performance was defined as the standard deviation of the asynchronies across all beats in a given each trial.

---

# EEG Data Description

For each EEG dataset within each pair’s folder:

- Channels 1–32: left participant EEG
- Channels 33–64: right participant EEG

Data are stored in BrainVision format.

---

# Event Codes (Test Section)

The following event markers are present during the test section (see Figure 1 for schematic reference):

- **S1** – the beginning of the test trials portion of the experiment  
- **S10** – a condition marker indicating the beginning of a block of musical duets  
- **S11** – a condition marker indicating the beginning of a block of constant pitch sequences  
- **S105** – the start of each trial, triggered by pressing the space bar  
- **S128** – The first five S128s mark the metronome tone onsets. Remaining S128s mark the tone onsets from the left participant’s e-music box.  
- **S4** – tone onsets from the right participant’s e-music box 
- **S2** – the end of the left participant’s performance, marked one beat after the last of their 16-beat tone sequence  
- **S3** – the end of the right participant’s performance, marked one beat after the last of their 16-beat tone sequence   
- **S106** – the end of each trial after the rating scales were completed  
- **S107** – the end of each block  

---

# Figure

![Illustration of the event codes occurring over time in the dataset.](derivatives/figures/Figure1_EventCodes.png)

---

# Notes

- Data are organized in BIDS format.
- BrainVision files (.eeg, .vhdr, .vmrk) contain raw hyperscanning EEG data.
- Behavioural data are provided per pair and as a compiled dataset in the derivatives folder.
