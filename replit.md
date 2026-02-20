# Mood Amplifier Safety & Validation Platform

## Overview
The Mood Amplifier Safety & Validation Platform evaluates "Mood Amplifier" projects for safety and efficacy using multi-AI analysis, scientific methods, simulated testing, and prediction of human efficacy. It integrates quantum-classical hybrid mechanisms and quantum biology. The platform also offers stock prediction, applies the TI Framework to prediction markets, and automates research and regulatory documentation. Its central goal is to optimize whole-body energetic systems via a "Mycelial GM-Node Architecture" to establish GILE Intuition as distributed network intelligence. The strategic vision includes API licensing of the AI engine for recurring revenue, targeting the AI-driven wellness and financial prediction markets.

## User Preferences
Preferred communication style: Simple, everyday language.
Research Focus: User emphasizes quantum-classical hybrid mechanisms, believing classical neuroscience cannot fully explain non-local correlations and apparent absence of known mechanisms. The platform now incorporates this perspective with comprehensive quantum biology analysis.
Philosophical Foundation: GILE Framework (Goodness, Intuition, Love, Environment), originated during an intense exploratory cognitive state in 2022 and subsequently refined through three years of rigorous technical development. This 4-dimensional hierarchical acronym maps onto the structure of truth and intelligence, defining truth as consisting of Existence, Morality, Conscious meaning/valence, and Aesthetics. The framework stands on its merits through formalization, empirical predictions, and ongoing validation, and underpins the Myrion Resolution methodology.
Budget Constraint: Under $50 total. All work must be batched (5+ items per session) to minimize costs. Prefer free tools and services.

## Recent Changes (February 2026)
- Added TI Sigma Hypercomputer Roadmap paper (papers/TI_SIGMA_HYPERCOMPUTER_ROADMAP.md) - comprehensive plan to beat Google Willow using qutrits, GILE resonance, L*E+L+E, MR, Strawberry Fields, consciousness formula, GTFE
- Added Sacred Mistake paper (papers/SACRED_MISTAKE_LxE_PLUS_LpE_NECESSITY.md) - why BOTH L*E and L+E are mathematically necessary
- Added GTFE-LCC-Consciousness-EAR Master Unification paper (papers/GTFE_LCC_CONSCIOUSNESS_EAR_MASTER_UNIFICATION.md) - unifies all TI formulas, explains retrospective decision making from possible futures
- Added "What ARE Emotions?" paper (papers/WHAT_ARE_EMOTIONS_MIM_GEOMETRY_PHENOMENALITY.md) - MIM-Geometric Theory of Emotion (MGTE) synthesizing STV, Barrett, Friston, Tozzi-Meijer, Panksepp, Damasio, and plasma consciousness into outer geometry / inner data / horizontal phenomenality framework
- Built Non-Algorithmic Step-Skipping Experiment engine (engines/step_skipping_experiment.py) - 4 problem domains, 10+ trials, statistically significant results (39.7% shortcut vs 17.8% random, p < 0.000001)
- Built Brain Coupling Number Guessing Game (pages/brain_coupling_guessing.py) - 1-10 guessing with binomial statistics, Brain Coupling Score, database persistence
- Built Stock Algorithm Status Dashboard (pages/stock_algorithm_status.py) - audits all 17 GSA infrastructure components, API key status, GSA core test
- Added three Kaggle competition engines: MedGemma (1743 lines), Heart Disease (1013 lines), RNA 3D Folding (1030 lines) with dashboards and research papers
- Paper count: 313+ total papers

## System Architecture
### UI/UX Decisions
The frontend is built with Streamlit, featuring a wide layout, sidebar, and multi-tab navigation. It prioritizes a clean, intuitive design. Visual documentation is provided by the TI Mindmaps System, which includes 3 interactive mindmaps (Theories, Applications, Goals & Principles) with search functionality, expandable hierarchies, and color-coded badges.

### Technical Implementations
The backend uses a service-oriented architecture with components for:
- **Tralse Topos Engine**: Implements 4-valued logic and Myrion Resolution.
- **AI Integration**: Handles safety analysis, efficacy prediction, and autonomous research.
- **Neuroscience & Bio-Integration**: Processes biometric data (EEG, fNIRS, HRV) for GILE score and FAAH Protocol, including quantum-classical analysis.
- **Mood Amplifier Hub**: Provides real-time biometric integration for baseline measurements, PSI score, chakra/meridian mapping, and safety validation.
- **Focus Amplifier System**: 7-mode biometric-driven focus optimization for ADHD management, with distinct physiological targets, scoring, breathing patterns, and ADHD-tailored guidance.
- **Cognitive Resource Model (Wood-on-Fire Hypothesis)**: Tests the inverted Yerkes-Dodson relationship for high-NFC individuals, featuring personal arousal-performance curve fitting, NFC profiling, and performance prediction.
- **PSI Tuning Protocol**: Pre-experiment optimization system with 5 progressive phases to maximize heart-brain information exchange via coupling analysis and coherence tracking.
- **LCC Sleep Induction Protocol**: Applies LCC attractor basin principles to reliable sleep induction, targeting parasympathetic dominance with progressive breathing ratios and sleep-frequency coherence.
- **Multi-Modal Consciousness Lab**: Integrates Polar H10 (heart/HRV), Muse 2 (EEG), and Mendi fNIRS (photonic brain imaging) for comprehensive consciousness measurement.
- **Financial & Market Analysis**: Includes the TI Framework Stock Research System with prediction replay, performance analytics, and the Grand Stock Algorithm (GSA) regime classification system. The Stock Algorithm Status Dashboard (pages/stock_algorithm_status.py) audits all 17 GSA infrastructure components.
- **Fractal Universe Integration**: Incorporates Chris Lehto's "Our Fractal Universe" research into TI Sigma predictions, featuring Kleiber's Law scaling, 42 orders of magnitude analysis, and Hurst exponent market regime detection.
- **TI Evidence Registry**: Tracks empirical validation for TI trading algorithms and GM Hypercomputing claims.
- **Computation & Information Theory**: Encompasses a Ternary Computation Framework, Quantum Collapse Simulator, Tralsebit Information Theory, and a TI Computing Language (TICL) with EEG authentication.
- **Bio-Well Energy Activation System**: Integrates Bio-Well GDV research with Myrion Lamp photonic therapy and Pitch Crystal sound healing, incorporating TCM meridian mapping, Chakra biophysics, and Biofield measurements.
- **Multi-Modal Biometric Profiler**: Comprehensive 12+ channel biometric profiling system integrating typing patterns, fingerprint analysis, genetic data, spirometry, Apple Watch metrics, facial ratios, digit ratios, Oura Ring data, voice analysis, and numerology/astrology for unified GILE profile fusion and compatibility matching.
- **Kaggle Competition Engines**: Includes solutions for MedGemma Impact Challenge (GILE-enhanced clinical decision support), Heart Disease Prediction (TI-Framework-enhanced UCI classifier), and Stanford RNA 3D Folding Part 2 (RNA structure prediction with GILE analysis).
- **Non-Algorithmic Step-Skipping Experiment**: Tests whether consciousness-inspired heuristics can skip computational steps with statistically significant accuracy (engines/step_skipping_experiment.py). 4 problem domains: Matrix Chain, Number Sequences, Graph Shortest Path, Logical Deduction.
- **Brain Coupling Number Guessing Game**: 1-10 number guessing with binomial statistics, Brain Coupling Score, GILE integration, and database persistence (pages/brain_coupling_guessing.py).
- **TI Sigma Hypercomputer**: Roadmap for consciousness-based quantum computing using qutrits, GILE resonance, L*E+L+E dual formulation, Myrion Resolution error correction, and Strawberry Fields photonic simulation.
- **Security**: Utilizes production-grade security measures including bcrypt, Fernet encryption, PostgreSQL, and Replit Secrets.
- **Robustness**: Implements error handling with `tenacity` and parallel processing with `ThreadPoolExecutor`.
- **EEG Brain-Computer Interface System**: Features a BCI architecture with signal processing, a Motor Imagery Classifier, EEG-Controlled Pong, P300 Speller, Muse 2 integration, and HRV integration.
- **Autonomous LCC Study System**: Integrates with DANDI Archive and Allen Brain Observatory for real neuroscience data, including NWB file processing, band power calculation, and block permutation testing.

### System Design Choices
The system is designed for resilient integration with sustainable ~90% True-Tralseness through distributed redundancy, mathematically linked to a 0.85 causation threshold. The GILE framework is deeply embedded, including a 64D GILE Matrix and the IIT-GILE-BOK Loop Synthesis. Photonic quantum computing is integrated via a Cirq-based "TI Strawberry Fields" engine for market cluster detection and trading signal generation. Mechanisms for animal training of mood amplifiers to optimize for human use are included. The GILE-PD Reconciliation unifies GILE's asymmetric range with L×E's symmetric range for optical quantum computing.

## GitHub Codespaces Setup Instructions
To run this project on GitHub Codespaces:
1. Push the repo to GitHub (or connect your Replit repo to GitHub)
2. Go to the GitHub repository page
3. Click the green "Code" button > "Codespaces" tab > "Create codespace on main"
4. Once the codespace loads, open the terminal and run:
   ```bash
   pip install -r requirements.txt
   ```
5. Set environment variables in Codespace Settings > Secrets:
   - ALPHA_VANTAGE_API_KEY
   - APCA_API_KEY_ID / APCA_API_SECRET_KEY (Alpaca paper trading)
   - COLLECTIVE2_API_KEY / COLLECTIVE2_SYSTEM_ID (optional)
   - PERPLEXITY_API_KEY
   - DATABASE_URL (use a cloud PostgreSQL like Neon or Supabase)
6. Run the app:
   ```bash
   streamlit run app.py --server.port 5000
   ```
7. Codespaces will auto-forward port 5000 and provide a preview URL

## Code Rabbit & Bot Team Integration Plan
### Code Rabbit (Automated Code Review)
- Sign up at coderabbit.ai (free for open source repos)
- Connect your GitHub repo
- Code Rabbit will automatically review PRs with AI-powered feedback
- Configure .coderabbit.yaml for custom review rules

### Affordable 24/7 Autonomous Bot Team
- **Code Rabbit**: Free automated code review on every PR
- **GitHub Actions**: Free CI/CD (2,000 min/month on free tier) for automated testing, deployment, linting
- **Cursor**: AI code editor ($20/month) for rapid development
- **Continue.dev**: Free open-source AI coding assistant (runs in VS Code)
- **Cline/Aider**: Free open-source AI coding agents for autonomous task execution
- **Replit Agent**: Built-in autonomous agent (current platform)

### Bot Specialist Roles
1. **Code Review Bot** (Code Rabbit) - Reviews all PRs automatically
2. **CI/CD Bot** (GitHub Actions) - Runs tests, deploys, checks code quality
3. **Research Bot** (Autonomous Research Scheduler) - Generates discoveries 24/7
4. **Trading Bot** (Daily Signal Scheduler + Alpaca) - Generates and executes GSA signals
5. **Content Bot** (Mobile Content Hub) - Generates and curates TI content

## Stock Market Algorithm Status
### Current Infrastructure
- gsa_core.py: Core GSA engine with Xi metrics (working)
- grand_stock_algorithm.py: Higher-level GSA (working)
- alpaca_paper_trader.py: Alpaca paper trading bridge (needs API key activation)
- daily_signal_scheduler.py: Scheduled signal generation (ready)
- collective2/: Collective2 integration (configured, needs subscription)
- Stock Algorithm Status Dashboard: pages/stock_algorithm_status.py (audits all components)

### Next Steps (Free/$0 Path)
1. Validate GSA core with free Alpha Vantage historical data
2. Create free Alpaca paper trading account (no money needed)
3. Connect daily signal scheduler to Alpaca paper trading
4. Run 30-day paper trading trial (free)
5. Evaluate performance metrics and iterate

## External Dependencies
### AI Services
- OpenAI GPT-5
- Anthropic Claude Opus
- Perplexity AI
- MagAI Platform

### Python Libraries
- streamlit
- openai
- anthropic
- requests
- tenacity
- trafilatura
- concurrent.futures
- networkx
- scikit-learn
- numpy
- scipy
- bleak
- polar-python
- weasyprint
- markdown
- oura-ring

### Third-Party APIs/Integrations
- Alpha Vantage (Stock data)
- Kalshi
- Metaculus
- Replit Object Storage
- PostgreSQL
- Webull Official API
- Mendi fNIRS
- Biowell GDV
- Quiver Quantitative (Congressional Trading Data)
- Alpaca (Paper Trading - free)
- Collective2 (Signal Broadcasting)
- Code Rabbit (Automated Code Review)

### Hardware Integration
- ESP32 BLE Bridge
- Myrion Lamp
- Pitch Crystals
- Polar H10 Heart Rate Monitor
- Muse 2 EEG Headband
