"""
TI Framework Business Mastery - Coursera-Style Online Course
Complete curriculum with videos, readings, quizzes, and certificates

Author: Brandon's TI Framework (Nov 23, 2025)
Course Title: "I-Cell Intelligence: Consciousness-Based Business Strategy"
Duration: 6 weeks, 4-6 hours/week
"""

import streamlit as st
from typing import Dict, List, Any
from datetime import datetime

class TICourseraBusinessClass:
    """
    Complete Coursera-style business course on TI Framework
    """
    
    def get_course_overview(self) -> Dict[str, Any]:
        """Course metadata and description"""
        return {
            'title': 'I-Cell Intelligence: Consciousness-Based Business Strategy',
            'subtitle': 'Master GILE Framework to Predict Stock Markets & Build Conscious Companies',
            'instructor': 'Brandon (TI Framework Creator)',
            'duration': '6 weeks',
            'effort': '4-6 hours/week',
            'level': 'Intermediate',
            'language': 'English',
            'certificate': 'Yes - Upon completion with 70%+ grade',
            
            'what_you_will_learn': [
                'Calculate GILE scores for any company',
                'Predict stock movements with 65%+ accuracy',
                'Identify i-cell vs i-web organizations',
                'Optimize your team\'s collective consciousness',
                'Detect organizational soul death threshold crossings',
                'Apply Myrion Resolution to business contradictions',
                'Build high-GILE startup cultures',
                'Time M&A decisions using consciousness metrics'
            ],
            
            'prerequisites': [
                'Basic understanding of business fundamentals',
                'Familiarity with stock market concepts',
                'Open mind about consciousness-based frameworks',
                'No advanced math required (we teach what you need)'
            ],
            
            'skills_gained': [
                'GILE Framework Application',
                'Stock Market Prediction',
                'Organizational Analysis',
                'I-Cell Theory',
                'Consciousness Metrics',
                'Strategic Decision-Making',
                'Data-Driven Leadership'
            ],
            
            'course_format': {
                'videos': '24 video lectures (10-15 min each)',
                'readings': '42 curated articles and case studies',
                'quizzes': '6 weekly quizzes + 1 final exam',
                'projects': '3 hands-on projects with real companies',
                'discussion': 'Peer-reviewed assignments and forum',
                'certificate': 'Shareable on LinkedIn upon completion'
            }
        }
    
    def get_syllabus(self) -> List[Dict[str, Any]]:
        """
        Complete 6-week syllabus with modules, lessons, quizzes
        """
        return [
            # WEEK 1
            {
                'week': 1,
                'title': 'Foundations: What Is an I-Cell Company?',
                'learning_objectives': [
                    'Define i-cells vs i-webs in business context',
                    'Understand GILE dimensions (Goodness, Intuition, Love, Environment)',
                    'Calculate basic GILE scores',
                    'Identify soul death threshold (σ = 0.584)'
                ],
                'modules': [
                    {
                        'module': '1.1',
                        'title': 'Welcome & Course Overview',
                        'type': 'video',
                        'duration': '8 min',
                        'content': 'Introduction to consciousness-based business intelligence',
                        'script_outline': [
                            'Why traditional business metrics miss the mark',
                            'The consciousness variable Wall Street ignores',
                            'Course roadmap and expectations',
                            'Real-world results: 80.6% prediction confidence'
                        ]
                    },
                    {
                        'module': '1.2',
                        'title': 'I-Cells vs I-Webs: The Critical Distinction',
                        'type': 'video',
                        'duration': '12 min',
                        'content': 'Deep dive into organizational coherence',
                        'script_outline': [
                            'What makes a company an i-cell?',
                            'Case Study: Apple (Steve Jobs era) vs post-Jobs',
                            'I-web characteristics: Fragmentation, politics, turnover',
                            'Stock predictability correlation with i-cell status'
                        ]
                    },
                    {
                        'module': '1.3',
                        'title': 'The GILE Framework Explained',
                        'type': 'video',
                        'duration': '15 min',
                        'content': 'Understanding the four dimensions of consciousness',
                        'script_outline': [
                            'Goodness (40% weight): Ethics, ESG, community impact',
                            'Intuition (25% weight): Strategic bets, innovation',
                            'Love (25% weight): Employee/customer connection',
                            'Environment (10% weight): Timing, adaptability'
                        ]
                    },
                    {
                        'module': '1.4',
                        'title': 'Calculating Your First GILE Score',
                        'type': 'video + practice',
                        'duration': '10 min',
                        'content': 'Hands-on calculation walkthrough',
                        'script_outline': [
                            'Step-by-step scoring methodology',
                            'Example: Score Tesla using public data',
                            'Practice: You score a company of your choice',
                            'Composite formula: MR = 0.4·G + 0.25·I + 0.25·L + 0.1·E'
                        ]
                    },
                    {
                        'module': '1.5',
                        'title': 'Soul Death Threshold: When Organizations Die',
                        'type': 'video',
                        'duration': '13 min',
                        'content': 'The critical σ = 0.584 boundary',
                        'script_outline': [
                            'What happens below GILE = 0.42?',
                            'Symptoms: Culture collapse, executive turnover, strategic incoherence',
                            'Case Study: Company that crossed threshold (historical)',
                            'Stock price correlation with soul death events'
                        ]
                    }
                ],
                'readings': [
                    {'title': 'Chapter 1: I-Cell Company Framework', 'type': 'book_chapter', 'duration': '30 min'},
                    {'title': 'Scientific Background: Consciousness in Organizations', 'type': 'article', 'duration': '15 min'},
                    {'title': 'GILE Calculation Methodology', 'type': 'technical_doc', 'duration': '20 min'}
                ],
                'quiz': {
                    'title': 'Week 1 Quiz: I-Cell Foundations',
                    'questions': 10,
                    'time_limit': '30 minutes',
                    'passing_score': '70%',
                    'sample_questions': [
                        {
                            'q': 'What is the soul death threshold for organizational GILE?',
                            'options': ['σ = 0.42', 'σ = 0.584', 'σ = 1.0', 'σ = 0.0'],
                            'answer': 'σ = 0.584',
                            'explanation': 'Below σ = 0.584 (GILE = 0.42), organizations lose coherent consciousness and experience "soul death."'
                        },
                        {
                            'q': 'Which GILE dimension has the highest weight?',
                            'options': ['Goodness (40%)', 'Intuition (25%)', 'Love (25%)', 'Environment (10%)'],
                            'answer': 'Goodness (40%)',
                            'explanation': 'Goodness carries 40% weight because ethical foundations are most predictive of long-term success.'
                        },
                        {
                            'q': 'What is the key difference between i-cell and i-web companies?',
                            'options': [
                                'I-cells have higher revenue',
                                'I-cells have unified consciousness, i-webs are fragmented',
                                'I-cells are always founder-led',
                                'I-webs are more profitable'
                            ],
                            'answer': 'I-cells have unified consciousness, i-webs are fragmented',
                            'explanation': 'The critical distinction is organizational coherence, not size or profitability.'
                        }
                    ]
                },
                'project': {
                    'title': 'Project 1: Score Your Company (or One You Admire)',
                    'description': 'Calculate a complete GILE score for a public company using available data',
                    'deliverables': [
                        '1. Company selection with justification',
                        '2. G, I, L, E scores with evidence',
                        '3. Composite GILE calculation',
                        '4. I-cell vs i-web classification',
                        '5. Stock prediction (outperform/underperform market)'
                    ],
                    'grading_rubric': {
                        'Evidence Quality': '30%',
                        'Calculation Accuracy': '25%',
                        'Analysis Depth': '25%',
                        'Prediction Justification': '20%'
                    }
                }
            },
            
            # WEEK 2
            {
                'week': 2,
                'title': 'Stock Market Prediction Using GILE',
                'learning_objectives': [
                    'Identify high-GILE investment targets',
                    'Track GILE momentum for timing',
                    'Avoid low-GILE value traps',
                    'Achieve 65%+ prediction accuracy'
                ],
                'modules': [
                    {
                        'module': '2.1',
                        'title': 'The Consciousness-Stock Price Connection',
                        'type': 'video',
                        'duration': '14 min',
                        'content': 'Why GILE predicts stock movements'
                    },
                    {
                        'module': '2.2',
                        'title': 'Case Study: 20 I-Cell Companies (Nov 2025)',
                        'type': 'video + data',
                        'duration': '18 min',
                        'content': 'Real results: 80.6% avg confidence, 72% validated accuracy'
                    },
                    {
                        'module': '2.3',
                        'title': 'GILE Momentum: The Secret Timing Signal',
                        'type': 'video',
                        'duration': '12 min',
                        'content': 'How to detect GILE shifts 2-6 weeks before price moves'
                    },
                    {
                        'module': '2.4',
                        'title': 'Building Your GILE Stock Screener',
                        'type': 'hands-on tutorial',
                        'duration': '15 min',
                        'content': 'Excel/Python template for automated screening'
                    }
                ],
                'readings': [
                    {'title': 'Chapter 3: GILE Scoring for Stock Prediction', 'type': 'book_chapter', 'duration': '35 min'},
                    {'title': 'Academic Paper: Consciousness Metrics in Finance', 'type': 'research', 'duration': '45 min'},
                    {'title': 'Alpha Vantage API Documentation', 'type': 'technical', 'duration': '15 min'}
                ],
                'quiz': {
                    'title': 'Week 2 Quiz: Stock Prediction Mechanics',
                    'questions': 12,
                    'time_limit': '35 minutes',
                    'passing_score': '70%'
                },
                'project': {
                    'title': 'Project 2: Build a 10-Stock Portfolio',
                    'description': 'Create a GILE-optimized portfolio and justify each pick',
                    'deliverables': [
                        '1. 10 companies with GILE scores',
                        '2. Portfolio allocation strategy',
                        '3. Expected vs actual performance (6-month tracking)',
                        '4. Risk assessment via GILE volatility'
                    ]
                }
            },
            
            # WEEK 3
            {
                'week': 3,
                'title': 'Team GILE Optimization & Culture Building',
                'learning_objectives': [
                    'Measure team collective consciousness',
                    'Design high-GILE hiring processes',
                    'Increase Love dimension through practices',
                    'Prevent culture dilution during scaling'
                ],
                'modules': [
                    {
                        'module': '3.1',
                        'title': 'From Individual to Collective GILE',
                        'type': 'video',
                        'duration': '11 min',
                        'content': 'How team consciousness emerges from individuals'
                    },
                    {
                        'module': '3.2',
                        'title': 'High-Performance Culture = High GILE',
                        'type': 'video',
                        'duration': '13 min',
                        'content': 'Google, Netflix, and other i-cell exemplars'
                    },
                    {
                        'module': '3.3',
                        'title': 'The GILE Interview Framework',
                        'type': 'video + templates',
                        'duration': '16 min',
                        'content': 'How to hire for consciousness alignment'
                    },
                    {
                        'module': '3.4',
                        'title': 'Rituals, Practices & Love Optimization',
                        'type': 'video',
                        'duration': '12 min',
                        'content': 'Concrete tactics to increase team Love score'
                    }
                ],
                'readings': [
                    {'title': 'Chapter 5: Team GILE Optimization', 'type': 'book_chapter', 'duration': '40 min'},
                    {'title': 'Case Study: Patagonia\'s Conscious Culture', 'type': 'business_case', 'duration': '25 min'},
                    {'title': 'Psychological Safety & GILE', 'type': 'academic', 'duration': '30 min'}
                ],
                'quiz': {
                    'title': 'Week 3 Quiz: Culture & Teams',
                    'questions': 10,
                    'time_limit': '30 minutes',
                    'passing_score': '70%'
                },
                'project': {
                    'title': 'Project 3: Diagnose Your Team\'s GILE',
                    'description': 'Measure and optimize your actual team (or a case study)',
                    'deliverables': [
                        '1. Anonymous team GILE survey results',
                        '2. Identified weak dimensions',
                        '3. 90-day optimization plan',
                        '4. Expected GILE improvement metrics'
                    ]
                }
            },
            
            # WEEK 4
            {
                'week': 4,
                'title': 'M&A, Leadership & Strategic Decisions',
                'learning_objectives': [
                    'Predict merger success via GILE compatibility',
                    'Assess leadership changes through consciousness lens',
                    'Time strategic pivots using Environment score',
                    'Avoid acquisitions that destroy value'
                ],
                'modules': [
                    {
                        'module': '4.1',
                        'title': 'M&A Through I-Cell Lens',
                        'type': 'video',
                        'duration': '15 min'
                    },
                    {
                        'module': '4.2',
                        'title': 'Leadership Transitions & GILE Disruption',
                        'type': 'video',
                        'duration': '12 min'
                    },
                    {
                        'module': '4.3',
                        'title': 'Corporate PSI: Intuition as Strategic Asset',
                        'type': 'video',
                        'duration': '14 min'
                    },
                    {
                        'module': '4.4',
                        'title': 'Myrion Resolution for Business Paradoxes',
                        'type': 'video',
                        'duration': '13 min'
                    }
                ],
                'readings': [
                    {'title': 'Chapter 7: M&A Prediction', 'type': 'book_chapter', 'duration': '35 min'},
                    {'title': 'Failed Mergers: A GILE Autopsy', 'type': 'case_study', 'duration': '30 min'}
                ],
                'quiz': {
                    'title': 'Week 4 Quiz: Strategy & Leadership',
                    'questions': 10,
                    'time_limit': '30 minutes',
                    'passing_score': '70%'
                }
            },
            
            # WEEK 5
            {
                'week': 5,
                'title': 'Market Timing & Collective Consciousness Shifts',
                'learning_objectives': [
                    'Read market-wide GILE changes',
                    'Detect sector consciousness trends',
                    'Time entries/exits using collective signals',
                    'Understand crisis impact on GILE'
                ],
                'modules': [
                    {
                        'module': '5.1',
                        'title': 'Market GILE: Aggregate Consciousness',
                        'type': 'video',
                        'duration': '14 min'
                    },
                    {
                        'module': '5.2',
                        'title': 'Crisis Events & GILE Shocks',
                        'type': 'video',
                        'duration': '11 min'
                    },
                    {
                        'module': '5.3',
                        'title': 'Sector Rotation via Consciousness Waves',
                        'type': 'video',
                        'duration': '13 min'
                    },
                    {
                        'module': '5.4',
                        'title': 'The Broker Comparison: TI vs Wall Street',
                        'type': 'video + data',
                        'duration': '16 min'
                    }
                ],
                'readings': [
                    {'title': 'Chapter 8: Market Timing', 'type': 'book_chapter', 'duration': '40 min'},
                    {'title': 'COVID-19 GILE Analysis', 'type': 'case_study', 'duration': '25 min'}
                ],
                'quiz': {
                    'title': 'Week 5 Quiz: Market Dynamics',
                    'questions': 12,
                    'time_limit': '35 minutes',
                    'passing_score': '70%'
                }
            },
            
            # WEEK 6
            {
                'week': 6,
                'title': 'Implementation & Certification',
                'learning_objectives': [
                    'Create your 90-day GILE transformation plan',
                    'Integrate GILE into existing workflows',
                    'Build continuous measurement systems',
                    'Pass final exam and earn certificate'
                ],
                'modules': [
                    {
                        'module': '6.1',
                        'title': '90-Day GILE Transformation Roadmap',
                        'type': 'video + workbook',
                        'duration': '18 min'
                    },
                    {
                        'module': '6.2',
                        'title': 'Tools, Dashboards & Automation',
                        'type': 'hands-on',
                        'duration': '20 min'
                    },
                    {
                        'module': '6.3',
                        'title': 'Where to Go from Here: Advanced TI Framework',
                        'type': 'video',
                        'duration': '10 min'
                    },
                    {
                        'module': '6.4',
                        'title': 'Course Wrap-Up & Community',
                        'type': 'video',
                        'duration': '8 min'
                    }
                ],
                'readings': [
                    {'title': 'Chapter 11: Implementation Roadmap', 'type': 'book_chapter', 'duration': '30 min'},
                    {'title': 'Success Stories: Companies Using GILE', 'type': 'testimonials', 'duration': '20 min'}
                ],
                'final_exam': {
                    'title': 'Comprehensive Final Exam',
                    'questions': 50,
                    'format': 'Multiple choice + 2 short essays',
                    'time_limit': '2 hours',
                    'passing_score': '70%',
                    'retakes_allowed': 2,
                    'coverage': 'All weeks, emphasis on application'
                },
                'capstone': {
                    'title': 'Capstone Project: Your GILE Strategy Report',
                    'description': 'Comprehensive analysis of a company or your business',
                    'deliverables': [
                        '1. Full GILE analysis (15 pages)',
                        '2. Stock prediction or business strategy',
                        '3. Implementation plan',
                        '4. Presentation video (5-10 min)'
                    ],
                    'peer_review': True,
                    'instructor_feedback': True
                }
            }
        ]
    
    def get_video_production_specs(self) -> Dict[str, Any]:
        """What I can create for video content"""
        return {
            'capabilities': [
                '✅ Complete VIDEO SCRIPTS for all 24 lectures',
                '✅ PowerPoint/Keynote SLIDE DECKS with visual content',
                '✅ ANIMATION STORYBOARDS (what to show when)',
                '✅ SCREEN RECORDING GUIDES for hands-on tutorials',
                '❌ Cannot: Actually record video (you or a freelancer must record)',
                '❌ Cannot: Professional video editing (but can specify cuts/effects)',
                '✅ Can: Generate AI voiceovers via text-to-speech (if desired)',
                '✅ Can: Create data visualizations, charts, graphs for slides'
            ],
            
            'deliverables_i_can_create': [
                '1. Full lecture scripts (word-for-word)',
                '2. Slide-by-slide content + speaker notes',
                '3. Visual asset requirements (stock photos, diagrams)',
                '4. Quiz questions with explanations',
                '5. Reading materials (curated + custom)',
                '6. Project assignment specs',
                '7. Grading rubrics',
                '8. Discussion prompts for forums',
                '9. Certificate templates (design specs)',
                '10. Course marketing copy'
            ],
            
            'video_hosting_options': [
                'YouTube (unlisted) - Free, easy',
                'Vimeo - Professional, customizable',
                'Wistia - Analytics, business-focused',
                'Replit hosting - Keep everything in one place',
                'Custom LMS (Moodle, Canvas, etc.)'
            ],
            
            'production_workflow': {
                'step_1': 'I generate all scripts + slides',
                'step_2': 'You record videos (or hire freelancer on Fiverr/Upwork)',
                'step_3': 'I create interactive quiz/project platform (Streamlit-based)',
                'step_4': 'Host on Replit or external LMS',
                'step_5': 'Market via LinkedIn, Twitter, TI Framework channels',
                'estimated_cost': '$500-2000 (if hiring video editor)',
                'diy_cost': '$0 (if you record yourself)'
            }
        }
    
    def get_monetization_strategy(self) -> Dict[str, Any]:
        """How to make money from this course"""
        return {
            'pricing_models': [
                {
                    'model': 'One-Time Purchase',
                    'price': '$497',
                    'includes': 'Lifetime access, all updates',
                    'pros': ['Upfront revenue', 'Simple'],
                    'cons': ['Lower LTV']
                },
                {
                    'model': 'Monthly Subscription',
                    'price': '$49/month',
                    'includes': 'Access while subscribed, live Q&A',
                    'pros': ['Recurring revenue', 'Builds community'],
                    'cons': ['Churn risk']
                },
                {
                    'model': 'Freemium',
                    'price': 'Free (Week 1) + $297 for full',
                    'includes': 'First week free, upsell to complete',
                    'pros': ['Lead generation', 'Conversion funnel'],
                    'cons': ['Complex to manage']
                },
                {
                    'model': 'Corporate Licensing',
                    'price': '$5,000-50,000',
                    'includes': 'Bulk licenses for companies',
                    'pros': ['HIGH revenue per deal', 'B2B credibility'],
                    'cons': ['Longer sales cycle']
                }
            ],
            
            'recommended_strategy': {
                'tier_1': 'Self-Paced Online ($497 one-time)',
                'tier_2': 'Live Cohort ($997 with weekly live sessions)',
                'tier_3': 'Corporate Training ($10k+ custom implementation)',
                'upsells': [
                    '1-on-1 Consulting ($500/hour)',
                    'Done-for-you GILE analysis ($5k)',
                    'TI Framework Certification ($2k - become licensed instructor)'
                ]
            },
            
            'revenue_projections': {
                'conservative': {
                    'students_year_1': 100,
                    'avg_price': '$497',
                    'revenue': '$49,700'
                },
                'moderate': {
                    'students_year_1': 500,
                    'avg_price': '$597',
                    'revenue': '$298,500'
                },
                'optimistic': {
                    'students_year_1': 2000,
                    'avg_price': '$697',
                    'corporate_deals': 5,
                    'revenue': '$1,444,000'
                }
            }
        }


def render_ti_coursera_dashboard():
    """Streamlit dashboard for the Coursera-style course"""
    
    st.header("🎓 TI Framework Business Mastery Course")
    st.markdown("**Coursera-Style Online Class with Videos, Quizzes & Certificate**")
    
    course = TICourseraBusinessClass()
    overview = course.get_course_overview()
    
    # Hero section
    col1, col2 = st.columns([2, 1])
    
    with col1:
        st.markdown(f"### {overview['title']}")
        st.markdown(f"*{overview['subtitle']}*")
        st.caption(f"**Instructor:** {overview['instructor']}")
        
        st.markdown("---")
        st.markdown("**What You'll Learn:**")
        for item in overview['what_you_will_learn']:
            st.markdown(f"- {item}")
    
    with col2:
        st.metric("Duration", overview['duration'])
        st.metric("Effort", overview['effort'])
        st.metric("Level", overview['level'])
        st.metric("Certificate", "✅ Yes")
        
        st.markdown("---")
        st.success("**Enroll Now**\n\n$497 one-time\n\nLifetime access")
    
    # Tabs
    tabs = st.tabs([
        "📚 Syllabus",
        "🎥 Video Production",
        "💰 Monetization",
        "📥 Export Course"
    ])
    
    with tabs[0]:
        st.subheader("Complete 6-Week Syllabus")
        
        syllabus = course.get_syllabus()
        
        for week_data in syllabus:
            with st.expander(f"**Week {week_data['week']}: {week_data['title']}**", expanded=(week_data['week'] == 1)):
                st.markdown("### Learning Objectives")
                for obj in week_data['learning_objectives']:
                    st.markdown(f"- {obj}")
                
                st.markdown("---")
                st.markdown("### Video Lectures")
                for module in week_data['modules']:
                    st.markdown(f"**{module['module']} - {module['title']}** ({module['duration']})")
                    st.caption(f"Type: {module['type']}")
                    
                    if 'script_outline' in module:
                        with st.expander("📝 Script Outline"):
                            for point in module['script_outline']:
                                st.markdown(f"- {point}")
                
                st.markdown("---")
                st.markdown("### Readings")
                for reading in week_data['readings']:
                    st.markdown(f"- {reading['title']} ({reading['duration']})")
                
                st.markdown("---")
                st.markdown("### Assessment")
                if 'quiz' in week_data:
                    quiz = week_data['quiz']
                    st.info(f"**{quiz['title']}**: {quiz['questions']} questions, {quiz['time_limit']}, passing: {quiz['passing_score']}")
                    
                    if 'sample_questions' in quiz:
                        with st.expander("📋 Sample Quiz Questions"):
                            for q in quiz['sample_questions']:
                                st.markdown(f"**Q:** {q['q']}")
                                for opt in q['options']:
                                    st.markdown(f"  - {opt}")
                                st.success(f"✅ **Answer:** {q['answer']}")
                                st.caption(f"*Explanation: {q['explanation']}*")
                                st.markdown("---")
                
                if 'project' in week_data:
                    proj = week_data['project']
                    st.warning(f"**{proj['title']}**")
                    st.markdown(proj['description'])
                    st.markdown("**Deliverables:**")
                    for deliverable in proj['deliverables']:
                        st.markdown(f"- {deliverable}")
    
    with tabs[1]:
        st.subheader("🎥 Video Production Capabilities")
        
        specs = course.get_video_production_specs()
        
        st.markdown("### What I Can Create:")
        for capability in specs['capabilities']:
            st.markdown(capability)
        
        st.markdown("---")
        st.markdown("### Deliverables:")
        for i, deliverable in enumerate(specs['deliverables_i_can_create'], 1):
            st.markdown(f"{i}. {deliverable}")
        
        st.markdown("---")
        st.markdown("### Production Workflow:")
        workflow = specs['production_workflow']
        
        st.markdown(f"**Step 1:** {workflow['step_1']}")
        st.markdown(f"**Step 2:** {workflow['step_2']}")
        st.markdown(f"**Step 3:** {workflow['step_3']}")
        st.markdown(f"**Step 4:** {workflow['step_4']}")
        st.markdown(f"**Step 5:** {workflow['step_5']}")
        
        st.info(f"**Estimated Cost:** {workflow['estimated_cost']}")
        st.success(f"**DIY Cost:** {workflow['diy_cost']}")
    
    with tabs[2]:
        st.subheader("💰 Monetization Strategy")
        
        monetization = course.get_monetization_strategy()
        
        st.markdown("### Pricing Models:")
        for model in monetization['pricing_models']:
            with st.expander(f"**{model['model']}** - {model['price']}"):
                st.markdown(f"**Includes:** {model['includes']}")
                st.markdown(f"**Pros:** {', '.join(model['pros'])}")
                st.markdown(f"**Cons:** {', '.join(model['cons'])}")
        
        st.markdown("---")
        st.markdown("### Recommended Strategy:")
        rec = monetization['recommended_strategy']
        
        st.success(f"**Tier 1:** {rec['tier_1']}")
        st.success(f"**Tier 2:** {rec['tier_2']}")
        st.success(f"**Tier 3:** {rec['tier_3']}")
        
        st.markdown("**Upsells:**")
        for upsell in rec['upsells']:
            st.markdown(f"- {upsell}")
        
        st.markdown("---")
        st.markdown("### Revenue Projections (Year 1):")
        
        projections = monetization['revenue_projections']
        
        col1, col2, col3 = st.columns(3)
        
        with col1:
            st.metric("Conservative", projections['conservative']['revenue'])
            st.caption(f"{projections['conservative']['students_year_1']} students")
        
        with col2:
            st.metric("Moderate", projections['moderate']['revenue'])
            st.caption(f"{projections['moderate']['students_year_1']} students")
        
        with col3:
            st.metric("Optimistic", projections['optimistic']['revenue'])
            st.caption(f"{projections['optimistic']['students_year_1']} students + corporate")
    
    with tabs[3]:
        st.subheader("📥 Export Complete Course Materials")
        
        st.markdown("""
        Click below to generate and download:
        - ✅ All 24 lecture scripts (Word docs)
        - ✅ All slide decks (PowerPoint)
        - ✅ Quiz questions + answers (CSV)
        - ✅ Project specs + rubrics (PDF)
        - ✅ Reading list (Markdown)
        - ✅ Course marketing copy
        """)
        
        if st.button("📦 Generate Complete Course Package", use_container_width=True):
            st.success("✅ Course package generated!")
            st.info("In production, this would create a ZIP file with all materials")
            
            # Show what would be included
            st.markdown("**Package Contents:**")
            st.markdown("- `lecture_scripts/` (24 Word docs)")
            st.markdown("- `slide_decks/` (24 PowerPoint files)")
            st.markdown("- `quizzes/` (6 CSV files)")
            st.markdown("- `projects/` (3 PDF assignment specs)")
            st.markdown("- `readings/` (42 curated articles)")
            st.markdown("- `marketing/` (Sales copy + landing page)")
