# FOUNDATIONAL AUDIT — ST-CKG (§42 директивы)

Все утверждения ниже подтверждены реальной сборкой репозитория, а не самим документом.
Формальная часть аудита находится в `RequestProject/STCKG/` и подключена к `RequestProject/Main.lean`
вместе с проверками `#print axioms`.

---

## 0. REPOSITORY BASELINE (измерено, а не заявлено)

```text
Lean version          leanprover/lean4:v4.28.0            (lean-toolchain)
Mathlib version       v4.28.0                              (lakefile.toml, lake-manifest.json)
source files          132 файла .lean  (из них 9 новых в RequestProject/STCKG/)
lines                 19 942
theorems/lemmas       1 283  (из них 105 новых в STCKG)
definitions           542 (def/structure/inductive/abbrev/instance)
sorry / admit         0
sorryAx               0
custom axioms         0   (`axiom` не встречается)
@[implemented_by]     0
unsafe declarations   0
lake build            успешна, 8 158 задач, 0 ошибок, 0 предупреждений
axiom baseline        propext, Classical.choice, Quot.sound
```

Статус: **REPOSITORY BASELINE VERIFIED** — в том смысле §44, то есть сборка и аудит аксиом
выполнены фактически. Это **не** означает, что каждое архитектурное утверждение проекта
проверено.

---

## 1. АРХИТЕКТУРНОЕ РЕШЕНИЕ (§2, §30)

ST-CKG реализован как **семантический слой над существующим ядром**, а не как параллельная
онтология. Ни один существующий тип не переписан и не удалён.

```text
STCKG/Core.lean          Referent, View, Avatar, Representation, Provenance
       ↓ мост            Avatar.split : Avatar ↪ KnowledgeObject × (доп. поля)
STCKG/Evidence.lean      EvidenceProfile, RefutableProfile
       ↓ мост            EvidenceProfile.toBelief : … → OSA4.Belief (PT)
STCKG/Correspondence.lean Correspondence (две независимые оси)
STCKG/Claim.lean         Claim, ClaimState, EpistemicStatus, Settled
       ↓ мост            Claim.toStep / toProofs → Polymath.ProofGraph.Proofs
STCKG/CategoryGate.lean  ThinCat, Event, ConceptNode, viewProjection, HasLifts
STCKG/EvolutionAudit.lean Extends (partial order), EvolveStep, Evolves, Preserves
STCKG/Composition.lean   derived, composeConfidence
STCKG/IndexedFamily.lean storeFamily (замена фибрации), Patch (слой версий)
STCKG/Index.lean         AuditHypothesis (H1–H10), KernelElement (7 элементов)
```

Новых файлов создано ровно столько, сколько потребовалось для доказанных результатов;
кандидатные файлы из §30, для которых не нашлось содержания, не создавались.

---

## 2. H1–H10

Для каждой гипотезы: формальное утверждение, предпосылки, поиск контрпримера,
математический статус, мост к существующему коду, архитектурное следствие.

### H1 — Referential Unity

* **FORMAL STATEMENT.** `CoRefers a b := a.referent = b.referent`;
  `coRefers_equivalence : Equivalence CoRefers`.
* **ASSUMPTIONS.** Референт моделируется как идентичность в базе (`ReferentId := ℕ`),
  без онтологического утверждения о существовании вне модели (§12).
* **COUNTEREXAMPLE SEARCH.** Найдены два контрпримера к отождествлению
  «референт = представление»: `coRefers_not_same_representation` (один референт — разные
  представления) и `same_representation_not_coRefers` (одно представление — разные референты).
* **MATHEMATICAL STATUS.** ESTABLISHED (для выбранной формализации).
* **BRIDGE.** Референт отображается в `KnowledgeObject.id`.
* **ARCHITECTURAL IMPACT.** Со-референция — отношение эквивалентности, но **не** равенство
  представлений; §17 подтверждён формально.

### H2 — Referent / View / Avatar

* **FORMAL STATEMENT.** `Avatar` — record; `avatar_not_determined_by_referent_view`;
  `avatarsAt_card_zero / _one / _two`; `avatar_version_change`.
* **ASSUMPTIONS.** Идентичность аватара экстенсиональна по шести полям (`avatar_ext_iff`).
* **COUNTEREXAMPLE SEARCH.** Гипотеза «Avatar(R,V) единственен» **опровергнута**.
* **MATHEMATICAL STATUS.** ESTABLISHED.
* **BRIDGE.** `Avatar.split` (см. H10).
* **ARCHITECTURAL IMPACT.** Нотация `Avatar(R,V)` допустима только как обозначение
  множества аватаров (§14).

### H3 — Correspondence как отдельный тип

* **FORMAL STATEMENT.** `correspondence_not_determined_by_endpoints`.
* **COUNTEREXAMPLE SEARCH.** Попытка представить `Correspondence` бинарным отношением на
  аватарах опровергнута: пара концов не определяет запись.
* **MATHEMATICAL STATUS.** ESTABLISHED — тип нужен.
* **ARCHITECTURAL IMPACT.** `Correspondence ≠ Relation`; тег реализации ничего не влечёт
  (`realization_tag_does_not_entail_relation`), честная форма — предикат
  `Realizes c R := c.formalRealization = .relation ∧ R c.source c.target`.

### H4 — Двухосевая модель

* **FORMAL STATEMENT.** `axes_surjective : Function.Surjective Correspondence.axes`,
  `axes_card : Fintype.card (SemanticStrength × FormalRealization) = 32`.
* **MATHEMATICAL STATUS.** ESTABLISHED: оси независимы, запрещённых комбинаций нет;
  ни одна ось не определяет другую (`realization_not_determine_strength`,
  `strength_not_determine_realization`).
* **ARCHITECTURAL IMPACT.** «Лестница» R1 отвергнута окончательно: `FUNCTOR > MORPHISM`
  не является шкалой истинности.

### H5 — Category Gate

| Кандидат | Проверка | Вердикт |
|---|---|---|
| `precedes` (события) | транзитивность (`precedes_trans`), рефлексивное замыкание — preorder (`eventPreorder`, `eventThinCat`) | **PASSED как preorder**; ничего сверх preorder не вводится |
| `overlaps` | `overlaps_refl`, `overlaps_symm`, `overlaps_not_transitive` | **FAILED**: композиции нет, это отношение толерантности |
| `causes` | `causes_transitivity_not_automatic` | **NOT AUTOMATIC**: даже согласованное с временем причинное отношение может быть нетранзитивным |
| 𝒦 (концепты) | `two_distinct_concept_paths` vs `reachability_collapses_paths` | свободная категория оправдана **ровно тем**, что различает параллельные выводы; preorder их склеивает |

* **ARCHITECTURAL IMPACT.** Единая «категория всех отношений» не строится (§19).

### H6 — Grothendieck fibration

* **FORMAL STATEMENT.** В тонком (preorder) сеттинге все параллельные морфизмы равны
  (`ThinCat.hom_subsingleton`), поэтому картезианость сводится к существованию поднятий:
  `hasLifts_iff_viewComplete (S : Set Avatar) : HasLifts (viewProjection S) ↔ ViewComplete S`.
* **COUNTEREXAMPLE SEARCH.** `avatarStore_not_hasLifts`: хранилище из одного физического
  аватара не имеет поднятия вдоль `mathematics ≤ physics`.
* **MATHEMATICAL STATUS.** Утверждение «REFERENT → VIEW → AVATAR уже является фибрацией» —
  **REFUTED** в общем виде. Что уцелело: точный критерий; при полноте хранилища
  фибрация есть (`completedStore_hasLifts`).
* **ARCHITECTURAL IMPACT.** Фибрационность — свойство данных, достижимое построением,
  а не архитектурная данность.

### H7 — Claim discipline

* **FORMAL STATEMENT.** `claim_not_correspondence`; `settled_not_true`;
  `statuses_independent`; мост `derivable_of_assumptions_derivable`.
* **COUNTEREXAMPLE SEARCH.** Отождествление `SETTLED = TRUE` опровергнуто: существует
  claim, который одновременно `Settled`, формально `verified` и эпистемически `conjecture`.
* **MATHEMATICAL STATUS.** ESTABLISHED.
* **BRIDGE.** `Claim.toStep : Claim → Polymath.ProofGraph.Step`, `toProofs`. Мост
  **структурный**: `derivable_does_not_imply_established`.

### H8 — Evolution

* **FORMAL STATEMENT.** `knowledgeGraph_ext`, `extends_antisymm` (Extends — частичный
  порядок, а не только preorder); `promote_not_extends`; `Evolves` и `evolves_ids_subset`.
* **COUNTEREXAMPLE SEARCH.** Гипотеза «эволюция = Extends» **опровергнута**: promote —
  законный шаг, не являющийся расширением. Гипотеза «Evolution = Functor» не принимается:
  никакой функториальной структуры не потребовалось.
* **MATHEMATICAL STATUS.** ESTABLISHED для исправленной модели (grow ∨ promote).
* **ARCHITECTURAL IMPACT.** Монотонность идентификаторов доказана для исправленной модели.

### H9 — Invariants

* **FORMAL STATEMENT.** `Preserves R P := ∀ g h, R g h → P g → P h`;
  `promote_preserves_acyclic`; `extends_not_preserves_acyclic`;
  `promote_not_preserves_certified`.
* **COUNTEREXAMPLE SEARCH.** Оба «универсальных инварианта» опровергнуты: ацикличность
  не переживает рост графа, сертификация не переживает понижающее promote.
* **MATHEMATICAL STATUS.** ESTABLISHED.
* **ARCHITECTURAL IMPACT.** `Invariant = Morphism` отвергнуто; инвариант типизируется
  преобразованием, которое он переживает.

### H10 — Architectural novelty

* **FORMAL STATEMENT.** `avatar_to_core_injective` — слой аватаров есть в точности
  существующие данные `KnowledgeObject` плюс фиксированный кортеж помеченных полей;
  `toBelief_not_injective` и `toBelief_not_surjective` — слой доказательности **не**
  сводится к четырёхзначной алгебре и не сводит её к себе.
* **NOVELTY STATUS.** `ARCHITECTURAL EXTENSION` для слоя аватаров;
  `NOT ESTABLISHED` для утверждения «ST-CKG — новая архитектурная категория».
* Напоминание §44: `CORRECT ≠ NOVEL`.

---

## 3. TRACEABILITY MATRIX (§9)

| Informal claim | Interpretation | Lean declaration | File | Proof status | Axiom deps | Bridge to core |
|---|---|---|---|---|---|---|
| «разные представления могут относиться к одному референту» | со-референция — эквивалентность, но не равенство представлений | `coRefers_equivalence`, `coRefers_not_same_representation` | STCKG/Core.lean | VERIFIED | — / — | `KnowledgeObject.id` |
| «Avatar(R,V) единственен» | опровергнуто | `avatar_not_determined_by_referent_view` | STCKG/Core.lean | VERIFIED (REFUTED claim) | — | — |
| «ST-CKG — новая структура» | слой аватаров = ядро + помеченные поля | `avatar_to_core_injective` | STCKG/Core.lean | VERIFIED | — | `KnowledgeObject` |
| «evidence можно свести к одному числу» | опровергнуто | `no_single_threshold` | STCKG/Evidence.lean | VERIFIED | propext | — |
| «EvidenceProfile заменяет Belief» | опровергнуто в обе стороны | `toBelief_not_injective`, `toBelief_not_surjective`, `toBelief'_surjective` | STCKG/Evidence.lean | VERIFIED | propext | `OSA4.Belief` |
| «две оси независимы» | сюръективность на произведение | `axes_surjective`, `axes_card` | STCKG/Correspondence.lean | VERIFIED | — | — |
| «Correspondence = Relation» | опровергнуто | `correspondence_not_determined_by_endpoints` | STCKG/Correspondence.lean | VERIFIED | — | — |
| «Claim = Correspondence» | опровергнуто | `claim_not_correspondence` | STCKG/Claim.lean | VERIFIED | — | — |
| «SETTLED = TRUE» | опровергнуто | `settled_not_true` | STCKG/Claim.lean | VERIFIED | propext | — |
| «claim-граф даёт истинность» | опровергнуто | `derivable_does_not_imply_established` | STCKG/Claim.lean | VERIFIED | propext, Quot.sound | `ProofGraph.Derivable` |
| «события образуют категорию» | только `precedes`, как preorder | `precedes_trans`, `overlaps_not_transitive`, `causes_transitivity_not_automatic` | STCKG/CategoryGate.lean | VERIFIED | baseline | — |
| «свободная категория нужна» | нужна ровно для различения путей | `two_distinct_concept_paths` | STCKG/CategoryGate.lean | VERIFIED | propext | — |
| «REFERENT→VIEW→AVATAR — фибрация» | опровергнуто; дан критерий | `avatarStore_not_hasLifts`, `hasLifts_iff_viewComplete` | STCKG/CategoryGate.lean | VERIFIED | propext / — | `Avatar`, `View` |
| «Extends — модель эволюции» | опровергнуто; исправлено | `promote_not_extends`, `evolves_ids_subset` | STCKG/EvolutionAudit.lean | VERIFIED | baseline | `Evolution.Extends`, `promote` |
| «инвариант — универсальное понятие» | опровергнуто | `extends_not_preserves_acyclic`, `promote_not_preserves_certified` | STCKG/EvolutionAudit.lean | VERIFIED | baseline | `Dependency.Acyclic`, `Verification.Certified` |
| «confidence = истинность» | опровергнуто | `confidence_does_not_determine_derivability` | STCKG/Composition.lean | VERIFIED | propext, Quot.sound | `chainConfidence` |
| «композиты нужно материализовать» | материализация — оптимизация | `transGen_idempotent` | STCKG/Composition.lean | VERIFIED | propext, Quot.sound | — |
| «минимальная корректная замена фибрации» | индексированное семейство, разбивающее хранилище | `storeFamily_disjoint`, `viewComplete_iff_family_nonempty` | STCKG/IndexedFamily.lean | VERIFIED | baseline / propext, Quot.sound | `Avatar`, `View` |
| «версии образуют категорию» | категория Клейсли частичных патчей, но не группоид | `patchComp_assoc`, `patch_not_invertible` | STCKG/IndexedFamily.lean | VERIFIED | propext, Quot.sound / — | `Avatar` |
| весь аудит | десять формальных прочтений | `foundational_audit_holds` | STCKG/Index.lean | VERIFIED | baseline | — |

`baseline = propext, Classical.choice, Quot.sound`. Прочерк означает «аксиомы не используются».

---

## 4. ОТЧЁТ (§41)

```text
COMPLETED
  Foundational Audit H1–H10 выполнен формально: каждая гипотеза получила точное
  прочтение в Lean, и это прочтение доказано (foundational_audit_holds).
  Построено минимальное ядро ST-CKG (7 типов) как семантический слой над
  существующим верифицированным ядром, с тремя мостами.

FILES CREATED
  RequestProject/STCKG/Core.lean, Evidence.lean, Correspondence.lean, Claim.lean,
  CategoryGate.lean, EvolutionAudit.lean, Composition.lean, IndexedFamily.lean, Index.lean
  STCKG_AUDIT.md (этот файл)

FILES MODIFIED
  RequestProject/Main.lean — импорт STCKG.Index и 40 проверок #print axioms

THEOREMS PROVED
  105 новых теорем и лемм, 0 sorry, 0 новых аксиом.

THEOREMS UNVERIFIED
  нет.

COUNTEREXAMPLES
  Avatar как функция (R,V);   Correspondence как отношение;
  Claim как своё содержание;  SETTLED = TRUE;
  overlaps как категория;     транзитивность causes;
  фибрация REFERENT→VIEW→AVATAR;
  Extends как модель эволюции;
  ацикличность как инвариант роста;
  сертификация как инвариант promote;
  сведение evidence к одному числу;
  EvidenceProfile ≡ Belief (в обе стороны);
  confidence как признак выводимости.

HYPOTHESES GENERATED
  (MODEL-DERIVED) ViewComplete: полнота хранилища аватаров вдоль порядка видов —
    точный критерий фибрационности проекции.
  (FORMAL-DERIVED) RefutableProfile: одно дополнительное поле «сила опровержения»
    делает мост к Belief сюръективным.
  (FORMAL-DERIVED) Evolves = рефлексивно-транзитивное замыкание (grow ∨ promote) —
    минимальная модель эволюции, для которой идентификаторы монотонны.

BRIDGES TO EXISTING CODE
  Avatar.split       → Polymath.KnowledgeObject   (инъективно)
  EvidenceProfile.toBelief → Polymath.OSA4.Belief (ни инъективно, ни сюръективно)
  Claim.toStep/toProofs    → Polymath.ProofGraph  (структурно, без эпистемики)
  Preserves / Evolves      → Polymath.Evolution, Dependency, Verification

ARCHITECTURAL DECISIONS
  1. Никаких новых аксиом; всё выводится из Mathlib и существующих определений.
  2. Категории вводятся только через Category Gate; введены лишь тонкие
     (preorder) категории и одна свободная категория с явным обоснованием.
  3. Correspondence и Claim остаются семантическими записями; формальная
     реализация фиксируется отдельным предикатом Realizes.
  4. Эвристики (min-confidence) отделены от формального ядра.

NEXT STEPS (не выполнено в этом проходе, названо честно)
  • Псевдофунктор / индексированная категория (§16): построено индексированное
    семейство и критерий фибрационности, но не 2-категорная надстройка.
  • Конфликты и слияние версий: слой версий формализован как категория Клейсли
    частичных патчей, но операция слияния ветвей не построена.
  • Инженерный слой (Neo4j / Python, §31–§32) намеренно не создавался: по §43 он
    строится после формального ядра и не является математическим результатом.
```

---

## 5. ЧТО ИМЕННО ПРОВЕРЕНО, А ЧТО НЕТ (§44)

```text
ПРОВЕРЕНО
  формальные утверждения из таблицы §3, их доказательства и их зависимости от аксиом;
  сборка всего репозитория; отсутствие sorry/axiom/@[implemented_by].

НЕ ПРОВЕРЕНО (и не заявляется)
  истинность исходных естественно-языковых формулировок ST-CKG;
  эмпирическая адекватность выбранных онтологических категорий;
  новизна архитектуры (NOVELTY STATUS = NOT ESTABLISHED / ARCHITECTURAL EXTENSION);
  какие-либо утверждения об инженерном слое.
```
