# Logic Field Theory v5 — Strain Theory

**Status:** draft-ready for repo  
**Purpose:** define the logical strain functional, its properties, and its role as a resolution-timing policy

---

## 0. Scope

This file introduces the **logical strain** functional $D$ on admissible states. Strain is used to model **when** resolution events occur. It does **not** set measurement outcome probabilities. Outcome weights are fixed in the probability module by a logical valuation on projections.

---

ah - I found the problem - when you do the code like this:

$$

v_N(G) = -\sum_{t} p(t) \log p(t).

$$

it doesn't render properly, but when you do this:

$$ v_N(G) = -\sum_{t} p(t) \log p(t).$$

it does

## 1. Definition

For an admissible configuration $G \in \mathcal{A}$, define

$$D(G)  =  w_I  v_I(G)\; +\; w_N  v_N(G)\; +\; w_E  v_E(G),$$

with nonnegative weights $w_I, w_N, w_E$.

- **$v_I$** internal-contradiction pressure. Increases as the shortest latent route to contradiction shrinks.  
- **$v_N$** non-classicality or structural indefiniteness. Entropic form, see below.  
- **$v_E$** external misfit with environmental or device constraints.

Interpretation: $D$ quantifies the logical “tension” carried by an epistemic description relative to classical definiteness and external constraints.

---

## 2. Structural requirements on $D$

For independent subsystems $G_1$, $G_2$ with disjoint symbols:

1. **Additivity:** $D(G_1 \oplus G_2)=D(G_1)+D(G_2)$.  
2. **Extensivity:** $D(n\cdot G)=n D(G)$ for $n$ i.i.d. copies.  
3. **Monotonicity:** adding latent contradiction routes or increasing misfit never reduces $D$.  
4. **Normalization:** $D(G)=0$ for classically definite, perfectly fitting configurations.  
5. **Continuity:** small structural edits change $D$ by a small amount.

These requirements constrain component forms without fixing a single numerical scale.

---

## 3. Entropic form for $v_N$

Let $p(t)$ be the empirical frequency of edge types in $G$ over a fixed alphabet of types. Impose:

- **Independence additivity** across disjoint subgraphs.  
- **Maximality** at uniform type distribution.  
- **Scale invariance** under graph replication.

Under these constraints, the unique functional up to a constant factor is the Shannon entropy:

$$

v_N(G)  =  -\sum_{t} p(t)  \log p(t).

$$

This does not assign probabilities to measurement outcomes. It measures internal structural indefiniteness of the description.

---

## 4. Resolution timing policy

Let a device or environment $E$ have a capacity threshold $\sigma_E > 0$. For an evolving state $|\psi\rangle$, define the **expected strain**

$$

\mathbb{E}_{\psi}[D]  =  \sum_{G\in\mathcal{A}} |\psi(G)|^2  D(G).

$$

**Policy.** A resolution event is triggered when $\mathbb{E}_{\psi}[D] > \sigma_E$. The process then implements a projection consistent with the probability valuation defined in the quantum structure module (Born weights).

- Strain sets **when**.  
- The valuation sets **how likely each outcome is**.

This separation prevents circularity with the Born rule.

---

## 5. Optional MaxEnt ensembles (not for Born weights)

For ensembles of descriptions governed by $D$, one can introduce a Maximum Entropy distribution over $\mathcal{A}$:

$$

\Pi(G)  =  \frac{e^{-\beta D(G)}}{Z},\quad Z=\sum_{H\in\mathcal{A}} e^{-\beta D(H)}.

$$

Use-cases: complexity weighting in simulation priors, device operating regimes, or heuristic sampling.  
Non-use: $\Pi$ is **not** the measurement probability rule for quantum outcomes.

---

## 6. Experimental hooks

Small departures in timing and decoherence rates can scale with average strain:

$$

\Gamma_{\text{eff}} \approx \Gamma_{0} \Big(1 + c  \frac{\mathbb{E}_{\psi}[D]}{\sigma_E}\Big).

$$

These are model-level targets for future protocols; the constants are platform-dependent and not fixed here.

---

## 7. Interfaces

- **Foundations:** relies on $\mathcal{A} = \mathbb{L}(\mathcal{S})$ and admissibility.  
- **Vector space embedding:** uses amplitudes $\psi(G)$ when taking expectations.  
- **Quantum structure:** defers to the projection valuation for outcome weights.  
- **Dynamics:** threshold can be evaluated along unitary evolution $|\psi(t)\rangle$.

---

## 8. For Lean formalization

- Define $v_I, v_N, v_E$ as functions on $\mathcal{A}$ with the properties above.  
- Prove additivity and extensivity lemmas for graph sums and replicas.  
- State the Shannon uniqueness of $v_N$ under the independence axioms.

---

## 9. Notes

- Keeping strain separate from probability is deliberate. It avoids building the Born rule into $D$ by hand.
