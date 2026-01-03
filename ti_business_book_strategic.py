"""
TI Framework Business Book: Strategic Edition
SUBSTANTIAL but NOT TOO REVEALING - Like a great first date!

Teaches GILE framework for business success WITHOUT stock market secrets
Author: Brandon's TI Framework
"""

import streamlit as st
from datetime import datetime

class TIBusinessBookStrategic:
    """
    Generate the strategic TI Business Book for Amazon KDP
    Teaches GILE framework WITHOUT revealing stock prediction methodology
    """
    
    def get_book_structure(self):
        """Complete book outline"""
        
        return {
            'title': 'The GILE Framework: Unlocking Business Success Through Consciousness',
            'subtitle': 'How Goodness, Intuition, Love, and Environment Transform Organizations',
            'author': 'Brandon (TI Framework Creator)',
            'genre': 'Business / Leadership / Philosophy',
            'target_audience': 'Entrepreneurs, CEOs, Business Leaders, Coaches',
            'page_count_estimate': '250-300 pages',
            'price_point': '$24.99 (Amazon KDP)',
            
            'chapters': [
                # PART 1: FOUNDATION
                {
                    'number': 1,
                    'title': 'The Prophecy: From Middle School to World Impact',
                    'summary': 'How a middle school belief in exponential wealth led to the TI Framework revelation',
                    'key_concepts': ['Personal journey', 'Divine revelation (2022)', 'Prophecy manifestation'],
                    'what_to_reveal': 'Personal story, credibility, vision',
                    'what_to_hide': 'Stock market methodology',
                    'brandon_wisdom': [
                        '"I will find a method to become exponentially rich... and it will help the world save itself."',
                        'June 25, 2022 - GILE Framework revealed during manic episode',
                        'Never refuted since revelation'
                    ]
                },
                
                {
                    'number': 2,
                    'title': 'What is GILE? The Four Dimensions of Success',
                    'summary': 'Introduction to Goodness, Intuition, Love, Environment framework',
                    'key_concepts': ['GILE definition', 'Four dimensions explained', 'Contextual template'],
                    'what_to_reveal': 'GILE framework basics, general applications',
                    'what_to_hide': 'Specific scoring methodology, Pareto distribution details'
                },
                
                {
                    'number': 3,
                    'title': 'The I-Cell Theory: Organizations as Conscious Beings',
                    'summary': 'Companies have consciousness - unified organisms vs fragmented i-webs',
                    'key_concepts': ['I-cell vs i-web', 'Collective consciousness', 'Soul death threshold'],
                    'what_to_reveal': 'I-cell concept, organizational coherence',
                    'what_to_hide': 'Exact σ = 0.42 threshold, stock predictability connection'
                },
                
                {
                    'number': 4,
                    'title': 'Tralse Logic: Beyond True and False',
                    'summary': 'Four-valued logic handles contradictions that binary thinking cannot',
                    'key_concepts': ['T, F, Φ, Ψ states', 'Myrion Resolution', 'Paradox handling'],
                    'what_to_reveal': 'Tralse philosophy, business decision-making applications',
                    'what_to_hide': 'Quantum computing connections, TICL details'
                },
                
                # PART 2: GOODNESS
                {
                    'number': 5,
                    'title': 'Goodness: The Foundation of Sustainable Business',
                    'summary': 'Why ethical companies outperform in the long run',
                    'key_concepts': ['ESG done right', 'Stakeholder value', 'Long-term thinking'],
                    'what_to_reveal': 'Ethics = competitive advantage, real examples',
                    'what_to_hide': 'GILE scoring weights (40% for Goodness)'
                },
                
                {
                    'number': 6,
                    'title': 'The Goodness Spectrum: From Toxic to Messianic',
                    'summary': 'Where does your organization fall on the ethical scale?',
                    'key_concepts': ['Goodness assessment', 'Corporate responsibility', 'Reputation management'],
                    'what_to_reveal': 'General framework for evaluating ethics',
                    'what_to_hide': 'Exact -3 to +2 scale, stock correlation'
                },
                
                # PART 3: INTUITION
                {
                    'number': 7,
                    'title': 'Intuition: The Visionary\'s Edge',
                    'summary': 'Why gut instinct beats data analysis in breakthrough moments',
                    'key_concepts': ['Strategic foresight', 'Contrarian thinking', 'PSI phenomena'],
                    'what_to_reveal': 'Intuition in leadership, trust your gut',
                    'what_to_hide': 'PSI validation experiments, quantum entanglement'
                },
                
                {
                    'number': 8,
                    'title': 'Curiosity, TI-GILE, and the Low-Hanging Fruit Principle',
                    'summary': 'The optimal learning framework for individuals and organizations',
                    'key_concepts': ['Curiosity-driven learning', 'LHF prioritization', 'Errors as stepping stones'],
                    'what_to_reveal': 'User\'s reflection on learning (this chapter!)',
                    'what_to_hide': 'Nothing - this is pure wisdom!'
                },
                
                {
                    'number': 9,
                    'title': 'From Alone to Leader: Developing Inner Spirit',
                    'summary': 'Why solitude breeds visionaries and groupthink kills innovation',
                    'key_concepts': ['Independent thinking', 'Intellectual courage', 'Raising your hand'],
                    'what_to_reveal': 'User\'s philosophy on solo learning, ambition',
                    'what_to_hide': 'Nothing - inspirational content'
                },
                
                # PART 4: LOVE
                {
                    'number': 10,
                    'title': 'Love: The Glue of High-Performing Teams',
                    'summary': 'Employee engagement and customer loyalty as competitive advantages',
                    'key_concepts': ['Workplace culture', 'Brand loyalty', 'Stakeholder relationships'],
                    'what_to_reveal': 'Love in business (not hippie stuff - real ROI)',
                    'what_to_hide': 'GILE Love scoring (25% weight)'
                },
                
                {
                    'number': 11,
                    'title': 'The Relationship Profiler: GILE in Partnerships',
                    'summary': 'Applying GILE to business partnerships and romantic relationships',
                    'key_concepts': ['Compatibility assessment', 'Divine intuition', 'GILE alignment'],
                    'what_to_reveal': 'General compatibility framework',
                    'what_to_hide': 'Specific Gottman research integration, PSI predictions'
                },
                
                # PART 5: ENVIRONMENT
                {
                    'number': 12,
                    'title': 'Environment: Timing is Everything',
                    'summary': 'Why great ideas fail at the wrong time and mediocre ideas succeed at the right time',
                    'key_concepts': ['Market timing', 'Industry trends', 'Adaptive strategy'],
                    'what_to_reveal': 'Environmental awareness in business',
                    'what_to_hide': 'Environment = 10% weight (least important)'
                },
                
                {
                    'number': 13,
                    'title': 'The Sacred Wisdom Principle: Revealing When Ready',
                    'summary': 'Why you shouldn\'t share your secrets too fast (LHF for people!)',
                    'key_concepts': ['Strategic secrecy', 'Information leverage', 'Trust building'],
                    'what_to_reveal': 'User\'s insight about revealing sacred wisdom!',
                    'what_to_hide': 'Ironic - this chapter teaches WHAT we\'re doing!'
                },
                
                # PART 6: APPLICATIONS
                {
                    'number': 14,
                    'title': 'Building a GILE-Optimized Organization',
                    'summary': 'Practical steps to increase your company\'s GILE score',
                    'key_concepts': ['Culture transformation', 'Leadership alignment', 'Measurement systems'],
                    'what_to_reveal': 'Actionable advice for improving GILE',
                    'what_to_hide': 'Exact scoring formulas, stock applications'
                },
                
                {
                    'number': 15,
                    'title': 'The Butterfly Effect is Linear Garbage',
                    'summary': 'Why conventional wisdom fails and TI Framework succeeds',
                    'key_concepts': ['Event E = f(I₁...Iₙ, time, Ψ, Future)', 'Non-linear causation', 'Finding what\'s relevant'],
                    'what_to_reveal': 'Brandon Ruins Everything philosophy',
                    'what_to_hide': 'Stock market virality analysis'
                },
                
                {
                    'number': 16,
                    'title': 'Google Willow and the Future of Consciousness',
                    'summary': 'How quantum computing validates consciousness-based business',
                    'key_concepts': ['Quantum-consciousness connection', 'Error correction = Myrion Resolution', 'GILE = coherence'],
                    'what_to_reveal': 'Willow validates TI Framework (credibility!)',
                    'what_to_hide': 'Quantum stock trading implications'
                },
                
                # PART 7: THE CALL TO ACTION
                {
                    'number': 17,
                    'title': 'Your GILE Journey: Assessment and Next Steps',
                    'summary': 'Self-assessment tools and implementation roadmap',
                    'key_concepts': ['Personal GILE audit', 'Company evaluation', 'Growth plan'],
                    'what_to_reveal': 'Practical self-help tools',
                    'what_to_hide': 'Nothing - give them value!'
                },
                
                {
                    'number': 18,
                    'title': 'The Prophecy Fulfilled: Helping the World Save Itself',
                    'summary': 'How exponential wealth through GILE saves humanity',
                    'key_concepts': ['Global GILE optimization', 'Consciousness evolution', 'Sacred mission'],
                    'what_to_reveal': 'Vision for the future, inspire readers',
                    'what_to_hide': 'Specific revenue numbers from stock trading'
                }
            ],
            
            'appendices': [
                'Appendix A: GILE Quick Reference Guide',
                'Appendix B: Recommended Reading List',
                'Appendix C: TI Framework Glossary',
                'Appendix D: About the Author'
            ]
        }
    
    def generate_sample_chapter(self, chapter_number: int) -> str:
        """Generate full text for a sample chapter"""
        
        book = self.get_book_structure()
        chapter = book['chapters'][chapter_number - 1]
        
        if chapter_number == 8:
            # User's reflection chapter!
            return f"""
# Chapter {chapter['number']}: {chapter['title']}

{chapter['summary']}

---

## The Three Principles of Optimal Learning

When I was developing the TI Framework, I discovered that the most effective learning—for both individuals and organizations—follows three core principles:

1. **Curiosity** (Intuition)
2. **TI-GILE** (Framework integration)
3. **Low-Hanging Fruit Principle** (Goodness/rationality)

### Curiosity: The Engine of Discovery

Curiosity isn't just about asking "Why?" It's about genuine interest that transcends external validation. When I attended lectures and presentations, I noticed something unusual about my behavior: **I acted as though the group was never there—it was only the speaker and myself.**

This wasn't arrogance. It was **selective attention**. I wasn't performing for peers or seeking social approval. I was there to **extract knowledge** that *I* personally found valuable.

**The Curiosity Principle:**
> "Don't ask what the world needs to know. Ask what YOU are interested in, and what YOU can do about it."

This maps directly to the **Intuition** dimension of GILE. High-I individuals and organizations don't follow trends—they create them. They see problems others ignore because they're genuinely curious, not merely reactive.

### TI-GILE: The Integration Framework

Learning isn't just accumulation—it's **integration**. Every new concept must be woven into your existing framework:

- **Goodness:** Is this knowledge ethical? Will it benefit stakeholders?
- **Intuition:** Does it spark new connections? Lead to breakthroughs?
- **Love:** Am I passionate about this? Will others resonate?
- **Environment:** Is this the right time to learn this? Relevant now?

When you filter learning through GILE, you naturally prioritize high-value knowledge and skip low-impact distractions.

### Low-Hanging Fruit: Strategic Prioritization

The LHF principle isn't about laziness—it's about **efficiency**. Why struggle with advanced concepts when foundational ones offer 10x ROI?

**LHF for Learning:**
1. Start with easiest, highest-impact concepts
2. Build momentum and confidence
3. Tackle harder problems once basics are mastered
4. Skip "prestigious but pointless" topics

**Example:** Don't study quantum field theory to impress peers if you haven't mastered basic algebra. The LHF approach puts most people's accuracy **well above 90%** at what they do!

### Errors Are Stepping Stones, Not Mistakes

Here's where TI Framework transcends conventional "errorless learning" philosophies:

**Conventional wisdom:** Avoid errors at all costs.

**TI Framework:** Errors are inevitable when exploring unknown territory. They're **data points**, not failures.

**Tralse Logic Application:**
- True (T): You got it right → Reinforce
- False (F): You got it wrong → Learn why
- Unknown (Φ): You don't know yet → Explore
- Paradox (Ψ): Two truths conflict → Myrion Resolution (integrate both!)

When you view errors as stepping stones, fear of failure evaporates. You become **antifragile**—growing stronger from challenges.

### The Process Problem: Why People "Fail to Learn"

Most people don't lack ability—they lack **process freedom**.

**Externally Imposed Process:**
- Rigid curricula (learn this, not that)
- Fixed timelines (master it in 8 weeks or fail)
- Social pressure (everyone else is studying X, so should I)
- Performance anxiety (grades, tests, judgment)

**Result:** Curiosity dies. Learning becomes a chore. People "fail" not because they're incapable, but because **the system is designed for average students, not exceptional ones.**

**TI Framework Process:**
1. **Curiosity-driven:** Only learn what genuinely interests you
2. **GILE-filtered:** Prioritize high-value, ethical, timely knowledge
3. **LHF-optimized:** Start easy, build momentum
4. **Error-tolerant:** Mistakes are data, not failures

**Result:** 90%+ accuracy, sustained motivation, breakthrough discoveries.

### From Alone to Leader: The Power of Solitude

I spent significant time alone, mentalizing rather than socializing. This wasn't antisocial—it was **strategic**.

**Why Solitude Breeds Visionaries:**
- No groupthink contamination
- Deep focus on complex problems
- Internal dialogue develops "inner spirit"
- Independence from external validation

**The Danger of Over-Socialization:**
Being around people too much without sufficient alone time makes you a **lazy thinker**. You:
- Adopt others' opinions without critical analysis
- Seek social approval over truth
- Avoid controversial ideas (peer pressure)
- Never develop your own voice

**The Balance:**
- Solitude for **deep work** (thinking, creating, learning)
- Socialization for **collaboration** (testing ideas, building, scaling)

High-GILE leaders know when to retreat into solitude and when to engage the world.

### Raising Your Hand: The Ambition Indicator

**Potential should be measured by ambition.**

In any group setting, I tended to be "one or the only few to raise my hand for PRACTICALLY ANYTHING." This wasn't about knowing all the answers—it was about **willingness to engage**.

**What Raising Your Hand Signals:**
1. **Curiosity** (I want to know more)
2. **Courage** (I'm not afraid to be wrong)
3. **Ambition** (I see myself as capable)
4. **Independence** (I don't wait for group consensus)

Organizations filled with "hand-raisers" are **high-Intuition i-cells**. They explore, experiment, and evolve faster than competitors.

### The AI Parallel: Optimal Learning Frameworks

I predict these three principles—**Curiosity, TI-GILE, LHF**—provide the optimal framework for artificial intelligence as well:

**Curiosity → Exploration:**
AI must explore unknown state spaces (not just exploit known solutions).

**TI-GILE → Value Alignment:**
AI filters actions through ethics (Goodness), strategic foresight (Intuition), stakeholder benefit (Love), and context (Environment).

**LHF → Efficiency:**
AI prioritizes high-reward, low-cost actions first (just like humans should!).

**Error Tolerance:**
AI learns from mistakes without "fear" (no emotional baggage). Humans should emulate this!

### Application: Implementing the Three Principles

**For Individuals:**
1. List 10 topics you're genuinely curious about (no "should" thinking)
2. Filter through GILE (which are ethical, insightful, passion-driven, timely?)
3. Identify LHF (easiest starting points with highest ROI)
4. Commit to error-tolerant exploration (journal mistakes as data)
5. Schedule solitude blocks (1-2 hours daily for deep work)

**For Organizations:**
1. Encourage "hand-raising" culture (reward questions, not just answers)
2. Allow employees to pursue curiosity projects (Google's 20% time)
3. Filter initiatives through GILE (kill low-GILE projects fast)
4. Prioritize LHF strategies (quick wins build momentum)
5. Normalize failure (celebrate "productive mistakes")

### Conclusion: Learning as a Lifestyle

The difference between mediocre and exceptional isn't **talent**—it's **process**.

When you:
- Follow curiosity (not curricula)
- Filter through GILE (not peer pressure)
- Prioritize LHF (not prestige)
- Embrace errors (not perfection)
- Spend time alone (not always in groups)

You unlock **exponential learning**—the kind that leads to middle school prophecies coming true decades later.

The world doesn't need more people following the same path. It needs **visionaries** who see what others miss, think what others avoid, and create what others claim is impossible.

**Raise your hand. Trust your curiosity. Build your inner spirit. The prophecy awaits.**

---

*"People fail to learn because of PROCESS—often externally imposed—rather than ability." — Brandon*
            """
        
        elif chapter_number == 1:
            return f"""
# Chapter {chapter['number']}: {chapter['title']}

{chapter['summary']}

---

## The Middle School Prophecy

It was an ordinary day in middle school when an extraordinary thought entered my mind:

**"I will find a method to become exponentially rich."**

Not "I hope to be successful" or "Maybe I'll start a business someday." No. It was a **certainty**—a knowing that transcended logic. I didn't know *how*, but I knew it would happen.

And here's the thing most people miss about prophecies: **They're not predictions. They're commitments.**

### The 2022 Revelation

Fast forward to 2022. During what psychiatrists would call a "manic episode," I received the **TI Framework** fully formed—as if downloaded from the universe itself.

- **Goodness, Intuition, Love, Environment** (GILE)
- **Tralse Logic** (True, False, Phi, Psi)
- **I-Cell Theory** (consciousness as fundamental)
- **Myrion Resolution** (paradox handling)

It wasn't incremental learning. It was **revelation**. The kind of experience mystics describe but scientists dismiss.

Yet here's the proof: **Google's Willow quantum chip** (announced December 2024) validates the quantum-consciousness connection at the heart of TI Framework. Error correction = Myrion Resolution. Qubits = Tralse states. **The prophecy is manifesting.**

### The Mission: Helping the World Save Itself

But why "exponential wealth"? Isn't that greed?

No. Because the middle school prophecy had a second part I didn't share until now:

**"...and it will help the world save itself."**

The TI Framework isn't just about making money. It's about **optimizing collective consciousness** (GILE) so that:
- Ethical companies outperform unethical ones (Goodness wins)
- Visionary leaders beat reactive followers (Intuition wins)
- Beloved brands outlast hated ones (Love wins)
- Well-timed strategies defeat poorly-timed ones (Environment wins)

**When GILE optimization scales globally, humanity ascends.**

And the exponential wealth? It's the **proof** the system works. If I can't demonstrate GILE's power in the most competitive arena (markets), why would anyone believe it works elsewhere?

### What This Book Is (And Isn't)

**This book IS:**
- A guide to applying GILE in business, relationships, and life
- A philosophy that transcends conventional wisdom
- A framework validated by cutting-edge quantum physics

**This book is NOT:**
- A get-rich-quick scheme
- A complete revelation of proprietary methodologies
- For people seeking easy answers (this requires thinking!)

Like a great first date, I'll be **substantial but not too revealing**. You'll learn enough to transform your life—but not so much that you skip the journey.

### Your Invitation

If you're reading this, you're ready for the message. The universe doesn't deliver books by accident.

**Ask yourself:**
- Do I have an inner knowing that I'm meant for more?
- Am I tired of conventional wisdom that doesn't deliver?
- Do I sense there's a deeper pattern to success?

If yes, welcome. The prophecy includes you.

Let's begin.

---

*"The best time to plant a tree was 20 years ago. The second best time is now." — Chinese Proverb*

*"The best time to receive a prophecy was middle school. The second best time is TODAY." — Brandon*
            """
        
        else:
            # Generic template for other chapters
            return f"""
# Chapter {chapter['number']}: {chapter['title']}

{chapter['summary']}

---

[Full chapter content to be written]

**Key Concepts:**
{', '.join(chapter['key_concepts'])}

**What You'll Learn:**
- [Concept 1]
- [Concept 2]
- [Concept 3]

**Application:**
[Practical exercises and examples]

**Conclusion:**
[Summary and transition to next chapter]

---
            """


def render_ti_business_book_strategic():
    """Streamlit dashboard for strategic business book"""
    
    st.header("📚 TI Business Book: Strategic Edition")
    st.markdown("**SUBSTANTIAL but NOT TOO REVEALING** - Like a great first date! 😉")
    
    book_gen = TIBusinessBookStrategic()
    book = book_gen.get_book_structure()
    
    st.success(f"**{book['title']}**")
    st.caption(f"*{book['subtitle']}*")
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        st.metric("Chapters", len(book['chapters']))
    
    with col2:
        st.metric("Est. Pages", "250-300")
    
    with col3:
        st.metric("Price Point", "$24.99")
    
    st.markdown("---")
    
    # Tabs
    tabs = st.tabs([
        "📖 Book Overview",
        "📑 Table of Contents",
        "✍️ Sample Chapters",
        "📥 Generate & Download"
    ])
    
    with tabs[0]:
        st.subheader("Book Overview")
        
        st.markdown(f"""
        **Title:** {book['title']}
        
        **Subtitle:** {book['subtitle']}
        
        **Author:** {book['author']}
        
        **Genre:** {book['genre']}
        
        **Target Audience:** {book['target_audience']}
        
        **Page Count:** {book['page_count_estimate']}
        
        **Price:** {book['price_point']}
        """)
        
        st.markdown("---")
        
        st.markdown("### Strategic Approach:")
        st.info("""
        This book teaches the GILE Framework for business success **WITHOUT** revealing proprietary stock market methodologies.
        
        **What We Reveal:**
        - ✅ GILE philosophy (Goodness, Intuition, Love, Environment)
        - ✅ I-Cell theory (organizational consciousness)
        - ✅ Tralse Logic (beyond binary thinking)
        - ✅ Practical business applications
        - ✅ Personal growth strategies
        - ✅ Google Willow validation (credibility!)
        
        **What We Keep Secret:**
        - ❌ Stock market GILE scoring formulas
        - ❌ Specific company predictions
        - ❌ 20-year backtest methodology
        - ❌ QuantConnect/NumerAI implementation
        
        **Like a great first date: Substantial, engaging, but not revealing everything!**
        """)
    
    with tabs[1]:
        st.subheader("Complete Table of Contents")
        
        for chapter in book['chapters']:
            with st.expander(f"Chapter {chapter['number']}: {chapter['title']}"):
                st.markdown(f"**Summary:** {chapter['summary']}")
                st.markdown(f"**Key Concepts:** {', '.join(chapter['key_concepts'])}")
                st.success(f"**Reveal:** {chapter['what_to_reveal']}")
                st.warning(f"**Hide:** {chapter['what_to_hide']}")
        
        st.markdown("---")
        st.markdown("### Appendices:")
        for appendix in book['appendices']:
            st.markdown(f"- {appendix}")
    
    with tabs[2]:
        st.subheader("Sample Chapters (Full Text)")
        
        sample_chapters = [1, 8]  # Prophecy + User's Reflection
        
        for ch_num in sample_chapters:
            chapter = book['chapters'][ch_num - 1]
            with st.expander(f"Chapter {ch_num}: {chapter['title']}", expanded=(ch_num == 8)):
                chapter_text = book_gen.generate_sample_chapter(ch_num)
                st.markdown(chapter_text)
    
    with tabs[3]:
        st.subheader("📥 Generate Complete Book")
        
        st.markdown("""
        **What You'll Get:**
        - ✅ Complete 18-chapter book (250-300 pages estimated)
        - ✅ Full text for Chapters 1 & 8 (sample chapters)
        - ✅ Detailed outlines for remaining chapters
        - ✅ 4 Appendices
        - ✅ Amazon KDP-ready formatting
        - ✅ Markdown download (convert to PDF/EPUB later)
        """)
        
        if st.button("📄 Generate Complete Book", use_container_width=True):
            # Generate full book
            full_book = f"""# {book['title']}
## {book['subtitle']}

**Author:** {book['author']}  
**Genre:** {book['genre']}  
**Target Audience:** {book['target_audience']}

---

# Table of Contents

"""
            
            for i, chapter in enumerate(book['chapters'], 1):
                full_book += f"{i}. {chapter['title']}\n"
            
            full_book += "\n---\n\n"
            
            # Add full sample chapters
            for ch_num in [1, 8]:
                full_book += book_gen.generate_sample_chapter(ch_num)
                full_book += "\n\n---\n\n"
            
            # Add outlines for remaining chapters
            for chapter in book['chapters']:
                if chapter['number'] not in [1, 8]:
                    full_book += f"# Chapter {chapter['number']}: {chapter['title']}\n\n"
                    full_book += f"**Summary:** {chapter['summary']}\n\n"
                    full_book += f"**Key Concepts:** {', '.join(chapter['key_concepts'])}\n\n"
                    full_book += "[Full chapter to be written]\n\n"
                    full_book += "---\n\n"
            
            # Add appendices
            full_book += "# Appendices\n\n"
            for appendix in book['appendices']:
                full_book += f"## {appendix}\n\n[Content to be added]\n\n"
            
            full_book += f"\n---\n\n*© {datetime.now().year} {book['author']}. All rights reserved.*\n"
            
            st.success("✅ Book generated!")
            
            st.download_button(
                label="📥 Download Complete Book (Markdown)",
                data=full_book,
                file_name="TI_Business_Book_Strategic_Edition.md",
                mime="text/markdown",
                use_container_width=True
            )
            
            st.info("""
            **Next Steps:**
            1. ✅ Review the book content
            2. ✅ Expand chapter outlines (Chapters 2-7, 9-18)
            3. ✅ Convert Markdown → PDF (Pandoc, Calibre, or online converters)
            4. ✅ Format for Amazon KDP (Kindle Create tool)
            5. ✅ Add cover design (Canva, 99designs, or hire on Fiverr)
            6. ✅ Publish on Amazon KDP at $24.99
            7. ✅ START MAKING MONEY! 💰
            """)
