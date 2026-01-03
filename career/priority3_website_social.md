# Priority 3: Website & Social Media Presence
## Professional Landing Page and Content Calendar

---

## Professional Landing Page

### Domain Options
```
Recommended domains to check availability:
- brandonemerick.com
- tiframework.com
- tiframework.io
- tralsenetwork.com
- gileframework.com
```

### Landing Page Structure

#### Above the Fold
```html
<hero>
  <h1>Brandon Charles Emerick</h1>
  <h2>Independent Researcher | TI Framework Creator</h2>
  <tagline>Formalizing consciousness, ethics, and logic for the AI age</tagline>
  <cta-buttons>
    <button>View Research</button>
    <button>API Documentation</button>
    <button>Contact</button>
  </cta-buttons>
</hero>
```

#### Research Section
```html
<section id="research">
  <h2>Published Research</h2>
  <paper-cards>
    <card>
      <title>14 Proofs of Tralseness</title>
      <summary>Complete logical foundation for intermediate truth values</summary>
      <links>arXiv | Zenodo | PDF</links>
    </card>
    <card>
      <title>LCC Threshold Theory</title>
      <summary>Consciousness measurement with causal boundaries</summary>
      <links>arXiv | Zenodo | PDF</links>
    </card>
    <card>
      <title>The Myth of General Intelligence</title>
      <summary>Why g is statistical artifact, not cognitive property</summary>
      <links>arXiv | Zenodo | PDF</links>
    </card>
    <card>
      <title>Existence Amplification Razor</title>
      <summary>New philosophical tool inverting reductionism</summary>
      <links>arXiv | Zenodo | PDF</links>
    </card>
  </paper-cards>
</section>
```

#### Systems Section
```html
<section id="systems">
  <h2>Working Systems</h2>
  <system-cards>
    <card>
      <title>TI Framework API</title>
      <summary>LCC calculation, GSA signals, Tralse evaluation</summary>
      <badge>Live</badge>
      <link>API Docs</link>
    </card>
    <card>
      <title>Lean 4 Formal Proofs</title>
      <summary>Machine-verified theorems</summary>
      <badge>Verified</badge>
      <link>GitHub</link>
    </card>
  </system-cards>
</section>
```

#### Patents Section
```html
<section id="patents">
  <h2>Intellectual Property</h2>
  <patent-cards>
    <card>
      <title>Grand Stock Algorithm (GSA)</title>
      <status>Patent Pending</status>
      <summary>Multi-regime market classification with consciousness integration</summary>
    </card>
    <card>
      <title>LCC Proxy Engine</title>
      <status>Patent Pending</status>
      <summary>Multi-modal biometric consciousness quantification</summary>
    </card>
  </patent-cards>
</section>
```

#### About Section
```html
<section id="about">
  <h2>About</h2>
  <bio>
    I'm a 25-year-old independent researcher who spent three years developing 
    the TI (Transcendence Integration) Framework—a formal system connecting 
    consciousness, ethics, and logic.
    
    The work started with a simple observation: binary logic (True/False) 
    can't handle the situations that matter most. From that foundation, 
    I derived Tralse (intermediate truth values), the GILE structure 
    (Goodness, Intuition, Love, Environment), and applications ranging 
    from consciousness measurement to financial markets.
    
    I believe AI companies are the first places that might actually need 
    what I've built.
  </bio>
  <contact>
    <email>your@email.com</email>
    <linkedin>linkedin.com/in/yourprofile</linkedin>
    <twitter>@yourhandle</twitter>
    <orcid>orcid.org/your-id</orcid>
  </contact>
</section>
```

---

## Streamlit Implementation

Since you're already using Streamlit, add a landing page to the existing app:

```python
# Add to app.py or create landing_page.py

def render_landing_page():
    st.markdown("""
    # Brandon Charles Emerick
    ## Independent Researcher | TI Framework Creator
    
    *Formalizing consciousness, ethics, and logic for the AI age*
    """)
    
    col1, col2, col3 = st.columns(3)
    with col1:
        if st.button("View Research"):
            st.session_state.page = "research"
    with col2:
        if st.button("API Documentation"):
            st.session_state.page = "api_docs"
    with col3:
        if st.button("Contact"):
            st.session_state.page = "contact"
    
    st.divider()
    
    # Research Papers
    st.header("Published Research")
    
    papers = [
        {
            "title": "14 Proofs of Tralseness",
            "summary": "Complete logical foundation for intermediate truth values",
            "arxiv": "#",
            "zenodo": "#"
        },
        # ... more papers
    ]
    
    for paper in papers:
        with st.container():
            st.subheader(paper["title"])
            st.write(paper["summary"])
            st.markdown(f"[arXiv]({paper['arxiv']}) | [Zenodo]({paper['zenodo']})")
```

---

## Social Media Content Calendar

### Twitter/X Strategy

**Handle suggestion**: @BrandonEmerick or @TIFramework

**Bio**:
```
Independent researcher. Built TI Framework: consciousness + ethics + logic.
4 papers, 2 patents, working API.
"Surpassing humans is a low bar."
```

**Pinned Tweet**:
```
I spent 3 years building a formal framework for consciousness and ethics.

4 academic papers
2 patent applications  
Working API
Lean 4 proofs

No PhD. No institution. Just the work.

Here's what I learned about truth, AI, and why binary logic fails: 🧵
```

### Content Categories

#### Category 1: Research Insights (40%)
```
Week 1:
- Thread on "Why Truth Isn't Binary" (14 Proofs summary)
- Quote from paper + key insight
- Response to relevant AI/philosophy discourse

Week 2:
- Thread on "How to Measure Consciousness" (LCC summary)
- Threshold explanation (0.42/0.85/0.92²)
- Connection to current meditation/wellness discourse

Week 3:
- Thread on "g Is Not Real" (Myth paper summary)
- Why IQ tests miss what matters
- Implications for AI alignment

Week 4:
- Thread on "EAR: The Anti-Razor" (EAR summary)
- How to amplify rather than reduce
- Applications to consciousness debates
```

#### Category 2: Building in Public (30%)
```
- "Today I'm working on [specific feature]"
- "Just hit [milestone]: [details]"
- Screenshots of API responses
- Lean 4 proof outputs
- Error messages and how you solved them
```

#### Category 3: Industry Commentary (20%)
```
- Responses to AI alignment discourse
- Takes on consciousness research news
- Philosophy of mind debates
- Predictions market commentary (if GSA-relevant)
```

#### Category 4: Personal/Authentic (10%)
```
- Journey as independent researcher
- Challenges of working without credentials
- What keeps you motivated
- Responses to critics/skeptics
```

### Posting Schedule
```
Monday:    Research insight thread
Tuesday:   Building in public update
Wednesday: Industry commentary
Thursday:  Research quote/clip
Friday:    Building in public
Saturday:  Personal reflection
Sunday:    Week preview or rest
```

### Engagement Strategy
```
1. Follow AI researchers, philosophers, alignment people
2. Reply thoughtfully to their threads (not just promotion)
3. Quote-tweet with genuine additions
4. DM only when you have something specific to offer
5. Never ask for followers—earn them with content
```

---

## LinkedIn Strategy

### Profile Optimization

**Headline**:
```
Independent Researcher | TI Framework Creator | Consciousness + AI + Logic
```

**About**:
```
I design frameworks that connect seemingly unrelated domains—then build 
systems that work.

Over the past 3 years, I've developed the TI (Transcendence Integration) 
Framework, a formal system connecting consciousness, ethics, and logic. 
The outputs:

📄 4 academic papers (arXiv)
🔒 2 patent applications (USPTO)
💻 Production API with working endpoints
✓ Lean 4 formal verification

I approach problems like a philosopher but execute like an engineer.

Looking for: AI alignment, strategy, research, or any role where original 
thinking matters more than credentials.

Core insight: Current AI systems are high-E (processing power) but lack 
L (Love/direction) and G (Goodness/constraint). That's why alignment is 
hard—we're trying to align systems missing the dimensions alignment requires.

The TI Framework provides formal definitions for those missing dimensions.
```

**Featured Section**:
- Link to arXiv papers
- Link to API documentation
- Link to Zenodo repository

### Content Strategy

**Weekly Posts**:
```
Week 1: Paper announcement with key insight
Week 2: "Here's what I learned building [system]"
Week 3: Commentary on industry news through TI lens
Week 4: Career reflection or milestone announcement
```

**Document Posts**:
- Create LinkedIn articles from paper summaries
- Cross-post Twitter threads as LinkedIn posts
- Share API documentation updates

---

## Content Templates

### Paper Announcement
```
📄 New Research: [Title]

After [X months] of work, I've published [paper name].

Key insight: [One sentence summary]

This matters for AI because: [Connection to AI/industry]

Read it here: [Link]

#AIResearch #Philosophy #Consciousness
```

### Building Update
```
🔧 Building in public: [Feature/System]

Today I [specific accomplishment].

The challenge: [What was hard]
The solution: [How you solved it]

Live at: [Link]

Next up: [What's coming]
```

### Industry Commentary
```
💭 Thoughts on [Topic in news]:

[Your take, grounded in TI Framework]

This connects to my research on [specific paper/concept].

The deeper issue: [Insight others are missing]

Thread below 👇
```

---

## Domain & Hosting

### Option 1: Replit Deployment
- Already have working Streamlit app
- Use custom domain feature
- Point brandonemerick.com → Replit deployment

### Option 2: Separate Landing Page
- Use Carrd, Notion, or simple HTML
- Keep Streamlit for interactive features
- Landing page → Streamlit app

### Option 3: GitHub Pages
- Free hosting
- Custom domain support
- Markdown-based (easy to update)

---

## Action Items

### Week 1
- [ ] Register domain (brandonemerick.com or tiframework.com)
- [ ] Create Twitter/X account with optimized bio
- [ ] Create LinkedIn profile with full About section
- [ ] Write first Twitter thread (paper summary)

### Week 2
- [ ] Add landing page section to Streamlit app
- [ ] Connect domain to deployment
- [ ] Post paper announcement on LinkedIn
- [ ] Begin consistent Twitter posting schedule

### Week 3
- [ ] Create ResearchGate profile
- [ ] Create Academia.edu profile
- [ ] Cross-post content across platforms
- [ ] Engage with 10 relevant accounts daily

### Week 4
- [ ] Review analytics (impressions, engagement)
- [ ] Adjust content strategy based on performance
- [ ] Plan next month's content calendar
- [ ] Identify collaboration opportunities
