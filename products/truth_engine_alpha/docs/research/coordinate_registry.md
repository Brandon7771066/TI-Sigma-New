# Provisional Coordinate Registry

This registry is provisional. Unresolved coordinates are deliberately left open so the model can continue to evolve.

## Truth Byte Coordinates

| name | current definition | positive pole | deficit pole | proposed PD range | measurement status | data source | validation status | primary category | known overlaps |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| TB-01 | claim specificity | explicit, narrow claim | vague claim | [0, 1] | heuristic | claim text | provisional | semantics | TB-02 |
| TB-02 | source attachment | cited source present | no citation | [0, 1] | heuristic | citation audit | provisional | provenance | TB-01 |
| TB-03 | contradiction pressure | conflict present | no conflict | [0, 1] | heuristic | contradiction graph | provisional | conflict | TB-04 |
| TB-04 | scaffolding readiness | clear route | unresolved ambiguity | [0, 1] | heuristic | scaffolding analysis | provisional | resolution | TB-03 |
| TB-05 | evidence directness | direct evidence | indirect evidence | [0, 1] | heuristic | evidence assessment | provisional | evidence | TB-06 |
| TB-06 | uncertainty burden | low uncertainty | high uncertainty | [0, 1] | heuristic | critical unknowns | provisional | uncertainty | TB-05 |
| TB-07 | actionability | actionable next step | no clear next step | [0, 1] | heuristic | recommended actions | provisional | operations | TB-08 |
| TB-08 | source spread | distributed sources | single-source concentration | [0, 1] | heuristic | source set | provisional | robustness | TB-07 |

## Existence Byte Coordinates

| name | current definition | positive pole | deficit pole | proposed PD range | measurement status | data source | validation status | primary category | known overlaps |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| EB-01 | decision relevance | decision-linked claim | non-decision claim | [0, 1] | heuristic | action ranking | provisional | criticality | EB-02 |
| EB-02 | downstream impact | high impact | low impact | [0, 1] | heuristic | action ranking | provisional | criticality | EB-01 |
| EB-03 | operational load | low load | high load | [0, 1] | heuristic | graph diagnostics | provisional | operations | EB-04 |
| EB-04 | instability | stable | unstable | [0, 1] | heuristic | crystal diagnostics | provisional | stability | EB-03 |
| EB-05 | uncertainty closure | closed uncertainty | open uncertainty | [0, 1] | heuristic | crystal diagnostics | provisional | uncertainty | EB-06 |
| EB-06 | resolution speed | fast | slow | [0, 1] | heuristic | evidence workflow | provisional | operations | EB-05 |
| EB-07 | auditability | auditable | opaque | [0, 1] | heuristic | report artifacts | provisional | compliance | EB-08 |
| EB-08 | reproducibility | reproducible | ad hoc | [0, 1] | heuristic | run logs | provisional | reproducibility | EB-07 |

## Myrion Byte Coordinates

| name | current definition | positive pole | deficit pole | proposed PD range | measurement status | data source | validation status | primary category | known overlaps |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| MB-01 | structural coherence | coherent | fragmented | [0, 1] | heuristic | crystal matrix | provisional | structure | MB-02 |
| MB-02 | support concentration | distributed support | concentrated support | [0, 1] | heuristic | claim graph | provisional | structure | MB-01 |
| MB-03 | contradiction separability | separable | entangled | [0, 1] | heuristic | graph errors | provisional | conflict | MB-04 |
| MB-04 | explanation depth | deep | shallow | [0, 1] | heuristic | crystal explanation | provisional | narrative | MB-03 |
| MB-05 | assumption sensitivity | well-conditioned | fragile | [0, 1] | heuristic | crystal diagnostics | provisional | stability | MB-06 |
| MB-06 | criticality routing | direct routing | diffuse routing | [0, 1] | heuristic | actions | provisional | operations | MB-05 |
| MB-07 | mismatch localization | localized | diffuse | [0, 1] | heuristic | graph errors | provisional | mismatch | MB-08 |
| MB-08 | benchmark alignment | aligned | misaligned | [0, 1] | heuristic | benchmark labels | provisional | evaluation | MB-07 |
| MB-09 | claim granularity | fine-grained | coarse | [0, 1] | heuristic | claims table | provisional | semantics | MB-10 |
| MB-10 | source granularity | fine-grained | coarse | [0, 1] | heuristic | sources table | provisional | provenance | MB-09 |
| MB-11 | evidence polarity | supportive | adverse | [0, 1] | heuristic | evidence assessment | provisional | evidence | MB-12 |
| MB-12 | scaffold coverage | covered | uncovered | [0, 1] | heuristic | scaffolding analysis | provisional | resolution | MB-11 |
| MB-13 | graph completeness | complete | incomplete | [0, 1] | heuristic | claim graph | provisional | graph | MB-14 |
| MB-14 | diagnostic completeness | complete | incomplete | [0, 1] | heuristic | crystal diagnostics | provisional | diagnostics | MB-13 |
| MB-15 | layered alignment | aligned | misaligned | [0, 1] | heuristic | crystal matrix | provisional | layering | MB-16 |
| MB-16 | release readiness | ready | not ready | [0, 1] | heuristic | verification summary | provisional | release | MB-15 |