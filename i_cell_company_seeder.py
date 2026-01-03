"""
I-Cell Company Seeder - Initial 20 Companies
Focuses on coherent i-cells with real-time KPIs for GILE baseline discovery
"""

from db_utils import db

# 20 I-CELL COMPANIES WITH REAL-TIME KPI POTENTIAL
I_CELL_COMPANIES = [
    # Tech I-Cells (Strong leadership, unified mission)
    {
        "ticker": "NVDA",
        "company_name": "NVIDIA Corporation",
        "sector": "Technology - Semiconductors",
        "is_i_cell": True,
        "coherence_score": 0.92,
        "leadership_stability_years": 31.0,  # Jensen Huang since 1993
        "has_realtime_kpis": True,
        "kpi_sources": {
            "earnings": "quarterly",
            "gpu_sales": "monthly",
            "datacenter_revenue": "quarterly"
        }
    },
    {
        "ticker": "TSLA",
        "company_name": "Tesla Inc.",
        "sector": "Automotive - Electric Vehicles",
        "is_i_cell": True,
        "coherence_score": 0.88,
        "leadership_stability_years": 20.0,  # Musk-driven since 2004
        "has_realtime_kpis": True,
        "kpi_sources": {
            "deliveries": "quarterly",
            "production": "quarterly",
            "energy_storage": "quarterly"
        }
    },
    {
        "ticker": "SHOP",
        "company_name": "Shopify Inc.",
        "sector": "Technology - E-commerce",
        "is_i_cell": True,
        "coherence_score": 0.85,
        "leadership_stability_years": 20.0,
        "has_realtime_kpis": True,
        "kpi_sources": {
            "gmv": "quarterly",
            "merchant_count": "quarterly"
        }
    },
    {
        "ticker": "AMD",
        "company_name": "Advanced Micro Devices",
        "sector": "Technology - Semiconductors",
        "is_i_cell": True,
        "coherence_score": 0.82,
        "leadership_stability_years": 10.0,  # Lisa Su since 2014
        "has_realtime_kpis": True,
        "kpi_sources": {
            "cpu_market_share": "quarterly",
            "datacenter_revenue": "quarterly"
        }
    },
    
    # Consumer I-Cells (Strong brand coherence)
    {
        "ticker": "COST",
        "company_name": "Costco Wholesale Corporation",
        "sector": "Consumer - Retail",
        "is_i_cell": True,
        "coherence_score": 0.94,
        "leadership_stability_years": 12.0,
        "has_realtime_kpis": True,
        "kpi_sources": {
            "membership_renewals": "monthly",
            "same_store_sales": "monthly",
            "total_members": "quarterly"
        }
    },
    {
        "ticker": "LULU",
        "company_name": "Lululemon Athletica",
        "sector": "Consumer - Apparel",
        "is_i_cell": True,
        "coherence_score": 0.87,
        "leadership_stability_years": 6.0,
        "has_realtime_kpis": True,
        "kpi_sources": {
            "comp_sales": "quarterly",
            "direct_consumer": "quarterly"
        }
    },
    {
        "ticker": "NKE",
        "company_name": "Nike Inc.",
        "sector": "Consumer - Apparel",
        "is_i_cell": True,
        "coherence_score": 0.83,
        "leadership_stability_years": 7.0,
        "has_realtime_kpis": True,
        "kpi_sources": {
            "digital_sales": "quarterly",
            "direct_sales": "quarterly"
        }
    },
    {
        "ticker": "SBUX",
        "company_name": "Starbucks Corporation",
        "sector": "Consumer - Restaurants",
        "is_i_cell": True,
        "coherence_score": 0.81,
        "leadership_stability_years": 2.0,
        "has_realtime_kpis": True,
        "kpi_sources": {
            "comp_store_sales": "quarterly",
            "active_rewards": "quarterly",
            "store_count": "quarterly"
        }
    },
    
    # Healthcare I-Cells (Mission-driven)
    {
        "ticker": "ISRG",
        "company_name": "Intuitive Surgical Inc.",
        "sector": "Healthcare - Medical Devices",
        "is_i_cell": True,
        "coherence_score": 0.90,
        "leadership_stability_years": 10.0,
        "has_realtime_kpis": True,
        "kpi_sources": {
            "procedures": "quarterly",
            "systems_installed": "quarterly"
        }
    },
    {
        "ticker": "DXCM",
        "company_name": "DexCom Inc.",
        "sector": "Healthcare - Medical Devices",
        "is_i_cell": True,
        "coherence_score": 0.86,
        "leadership_stability_years": 9.0,
        "has_realtime_kpis": True,
        "kpi_sources": {
            "users": "quarterly",
            "sensor_revenue": "quarterly"
        }
    },
    {
        "ticker": "VRTX",
        "company_name": "Vertex Pharmaceuticals",
        "sector": "Healthcare - Biotechnology",
        "is_i_cell": True,
        "coherence_score": 0.88,
        "leadership_stability_years": 9.0,
        "has_realtime_kpis": True,
        "kpi_sources": {
            "patient_count": "quarterly",
            "product_revenue": "quarterly"
        }
    },
    
    # Energy I-Cells (Clean tech focus)
    {
        "ticker": "NEE",
        "company_name": "NextEra Energy Inc.",
        "sector": "Energy - Renewable",
        "is_i_cell": True,
        "coherence_score": 0.84,
        "leadership_stability_years": 18.0,
        "has_realtime_kpis": True,
        "kpi_sources": {
            "renewable_capacity": "quarterly",
            "customer_growth": "quarterly"
        }
    },
    {
        "ticker": "ENPH",
        "company_name": "Enphase Energy Inc.",
        "sector": "Energy - Solar",
        "is_i_cell": True,
        "coherence_score": 0.82,
        "leadership_stability_years": 8.0,
        "has_realtime_kpis": True,
        "kpi_sources": {
            "microinverters_shipped": "quarterly",
            "energy_systems": "quarterly"
        }
    },
    
    # Financial I-Cells (Transparent mission)
    {
        "ticker": "V",
        "company_name": "Visa Inc.",
        "sector": "Financial - Payments",
        "is_i_cell": True,
        "coherence_score": 0.89,
        "leadership_stability_years": 12.0,
        "has_realtime_kpis": True,
        "kpi_sources": {
            "payment_volume": "quarterly",
            "processed_transactions": "quarterly"
        }
    },
    {
        "ticker": "MA",
        "company_name": "Mastercard Inc.",
        "sector": "Financial - Payments",
        "is_i_cell": True,
        "coherence_score": 0.87,
        "leadership_stability_years": 10.0,
        "has_realtime_kpis": True,
        "kpi_sources": {
            "gross_dollar_volume": "quarterly",
            "switched_transactions": "quarterly"
        }
    },
    
    # Industrial I-Cells (Innovation-focused)
    {
        "ticker": "CAT",
        "company_name": "Caterpillar Inc.",
        "sector": "Industrial - Machinery",
        "is_i_cell": True,
        "coherence_score": 0.80,
        "leadership_stability_years": 11.0,
        "has_realtime_kpis": True,
        "kpi_sources": {
            "machine_sales": "quarterly",
            "services_revenue": "quarterly"
        }
    },
    {
        "ticker": "DE",
        "company_name": "Deere & Company",
        "sector": "Industrial - Agricultural",
        "is_i_cell": True,
        "coherence_score": 0.81,
        "leadership_stability_years": 10.0,
        "has_realtime_kpis": True,
        "kpi_sources": {
            "equipment_sales": "quarterly",
            "precision_ag_revenue": "quarterly"
        }
    },
    
    # Software I-Cells (Platform coherence)
    {
        "ticker": "ADBE",
        "company_name": "Adobe Inc.",
        "sector": "Technology - Software",
        "is_i_cell": True,
        "coherence_score": 0.86,
        "leadership_stability_years": 13.0,
        "has_realtime_kpis": True,
        "kpi_sources": {
            "digital_media_arr": "quarterly",
            "creative_cloud_subs": "quarterly"
        }
    },
    {
        "ticker": "CRM",
        "company_name": "Salesforce Inc.",
        "sector": "Technology - Software",
        "is_i_cell": True,
        "coherence_score": 0.82,
        "leadership_stability_years": 25.0,  # Benioff since 1999
        "has_realtime_kpis": True,
        "kpi_sources": {
            "remaining_performance_obligation": "quarterly",
            "subscription_revenue": "quarterly"
        }
    },
    {
        "ticker": "NOW",
        "company_name": "ServiceNow Inc.",
        "sector": "Technology - Software",
        "is_i_cell": True,
        "coherence_score": 0.84,
        "leadership_stability_years": 7.0,
        "has_realtime_kpis": True,
        "kpi_sources": {
            "subscription_revenue": "quarterly",
            "current_rpg": "quarterly"
        }
    }
]

def seed_i_cell_companies():
    """Seed database with initial 20 i-cell companies"""
    print("🌱 Seeding i-cell companies database...")
    
    seeded_count = 0
    for company in I_CELL_COMPANIES:
        company_id = db.add_i_cell_company(
            ticker=company["ticker"],
            company_name=company["company_name"],
            sector=company["sector"],
            is_i_cell=company["is_i_cell"],
            coherence_score=company["coherence_score"],
            leadership_stability_years=company["leadership_stability_years"],
            has_realtime_kpis=company["has_realtime_kpis"],
            kpi_sources=company.get("kpi_sources")
        )
        
        if company_id:
            print(f"  ✅ {company['ticker']} - {company['company_name']}")
            seeded_count += 1
        else:
            print(f"  ❌ Failed: {company['ticker']}")
    
    print(f"\n✨ Seeded {seeded_count}/{len(I_CELL_COMPANIES)} i-cell companies!")
    return seeded_count

if __name__ == "__main__":
    seed_i_cell_companies()
