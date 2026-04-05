# Eneström–Kakeya Theorem in Isabelle/HOL

Formal proofs of the Eneström–Kakeya Theorem in Isabelle/HOL, produced
autonomously by Claude Code (Sonnet 4.6) as a case study in *vibe proving*.

- **EnestromKakeya1**: Proof via Rouché's theorem (765 lines)
- **EnestromKakeya2**: Elementary proof by contradiction (213 lines)

### Running find_facts

Index the relevant sessions, then start the server:

```bash
isabelle find_facts_index \
  HOL HOL-Library HOL-Complex_Analysis \
  HOL-Algebra HOL-Computational_Algebra HOL-Number_Theory

isabelle find_facts_server -p 8080 -v
```

Claude Code invokes find_facts via `./find-facts` against this local server.

## Paper 
For details, see the accompanying paper:

*Formalising the Eneström–Kakeya Theorem in Isabelle/HOL: a Vibe Proving Experiment from Scratch*.
