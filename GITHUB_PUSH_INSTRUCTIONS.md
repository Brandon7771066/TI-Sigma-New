# GitHub Push Instructions for GSA Algorithm

## Quick Push Commands

Run these in your terminal or on your local machine after cloning:

```bash
# If you haven't initialized git yet:
git init
git remote add origin https://github.com/YOUR_USERNAME/ti-gsa-algorithm.git

# Stage all files
git add .

# Commit with message
git commit -m "Add GSA algorithm with CI/CD validation and TI ontology"

# Push to main branch
git push -u origin main
```

## What Gets Pushed

### Core Algorithm
- `gsa_core.py` - Core GSA engine with GILE scoring
- `alpaca_paper_trader.py` - Alpaca paper trading integration
- `daily_signal_scheduler.py` - Scheduled signal generation

### Tests & CI
- `tests/test_gsa_core.py` - Unit tests
- `tests/test_gsa_backtest.py` - Backtest validation
- `.github/workflows/gsa_validation.yml` - GitHub Actions CI

### Documentation
- `research/TI_UNIFIED_ONTOLOGY.md` - TI framework integration
- `research/ONE_PHOTON_UNIVERSE_DE_INTERPRETATION.md` - Physics theory
- `ALPACA_DEPLOYMENT_GUIDE.md` - Trading deployment guide
- `README.md` - Project overview

## GitHub Actions Workflow

Once pushed, GitHub Actions will automatically:
1. Run unit tests on every push
2. Run backtest validation
3. Generate validation report
4. Run daily at 6 AM UTC

## Secrets Configuration

Add these secrets in GitHub repo settings (Settings → Secrets → Actions):

- `APCA_API_KEY_ID` - Your Alpaca API key
- `APCA_API_SECRET_KEY` - Your Alpaca secret key

## Verification

After pushing, check:
1. Actions tab → See workflow runs
2. Green checkmark = all tests passed
3. Red X = click to see what failed

## Repository Structure

```
ti-gsa-algorithm/
├── .github/
│   └── workflows/
│       └── gsa_validation.yml
├── tests/
│   ├── test_gsa_core.py
│   └── test_gsa_backtest.py
├── research/
│   ├── TI_UNIFIED_ONTOLOGY.md
│   └── ONE_PHOTON_UNIVERSE_DE_INTERPRETATION.md
├── gsa_core.py
├── alpaca_paper_trader.py
├── daily_signal_scheduler.py
├── ALPACA_DEPLOYMENT_GUIDE.md
└── README.md
```

## GitLab Alternative

If using GitLab (like your existing ti-sigma repo):

```bash
# Push to existing GitLab repo
git remote add gitlab https://gitlab.com/Brandon772/ti-sigma.git
git push gitlab main

# Or add GSA as subdirectory
cd ti-sigma
mkdir gsa
cp ../gsa_core.py gsa/
cp -r ../tests gsa/
git add gsa/
git commit -m "Add GSA trading algorithm"
git push origin main
```

## Next Steps After Push

1. ✅ Verify GitHub Actions runs successfully
2. ✅ Add secrets for Alpaca (if using for paper trading)
3. ✅ Share repo link with potential subscribers/investors
4. ✅ Reference in Collective2 strategy description
