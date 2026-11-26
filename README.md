# Math Chain Solver

A local symbolic solver with a replayable reasoning chain. Runs with Python 3.12 and the standard library. No build step, API keys, or network access are required.

Run from this directory:

    python -B -X utf8 run.py solve "sin(3*x)/x" --side both --out demo
    python -B -X utf8 run.py replay demo/run.json

The explanation is in demo/run.txt. Use python run.py --help for other commands.

For the integral and higher derivative examples, save this UTF-8 JSON array as tasks.json.

```json
[
  {"id":"integral","kind":"integrate","integrand":"2*x/(1+x^2)","variable":"x","parameters":[]},
  {"id":"nth-derivative","kind":"symbolic_order_derivative","function":"cos(3*t+1)*exp(2*t)","variable":"t","order":"n"}
]
```

Then run:

    python -B -X utf8 run.py batch tasks.json --out demo-batch
    python -B -X utf8 run.py replay demo-batch/integral.json
    python -B -X utf8 run.py replay demo-batch/nth-derivative.json

The bundle includes snapshot v157 and 329 executable rules. Some tasks remain unresolved.

## Worked examples

These chains are condensed from actual v157 runs. The commands above solve each problem and replay its saved proof.

### 1. Two-sided limit

$$
\lim_{x\to0}\frac{\sin(3x)}{x}=\boxed{3}
$$

1. Approach zero from the right with $x=t$ and from the left with $x=-t$, where $t\to0^+$.
2. Expand the sine on both sides. The numerators are $3t+o(t^2)$ and $-3t+o(t^2)$, respectively.
3. Divide by $t$ on the right and by $-t$ on the left. Both quotients are $3+o(t)$, so the two one-sided limits agree.

### 2. Indefinite integral

$$
\int\frac{2x}{1+x^2}\,dx=\boxed{\ln(1+x^2)+C}
$$

1. Set $Q=1+x^2$. Then $dQ=2x\,dx$, so the integrand becomes $dQ/Q$.
2. Integrate to get $\ln|Q|$. Since $Q>0$ for every real $x$, this is $\ln(1+x^2)$.
3. Differentiate the resulting antiderivative to recover $2x/(1+x^2)$ on the whole real line.

### 3. Derivative of order $n$

$$
\frac{d^n}{dt^n}\bigl(e^{2t}\cos(3t+1)\bigr)
=\boxed{(\sqrt{13})^n e^{2t}\cos(3t+1+n\phi)},
\qquad \phi=\arctan(3/2).
$$

1. Differentiate the pair $S=e^{2t}\sin(3t+1)$ and $C=e^{2t}\cos(3t+1)$ to get $S'=2S+3C$ and $C'=-3S+2C$.
2. Write the equations in the order $(C,S)$ and factor $\sqrt{13}$ out of their matrix. The remaining matrix is a rotation through $\phi$.
3. Iterate the matrix by induction. Each derivative multiplies the amplitude by $\sqrt{13}$ and adds $\phi$ to the phase.

## How it was built

AI agents using `gpt-6-astra`, `gpt-6.2-astra`, `gpt-6.1-sol`, and `gpt-6.2-sol` developed this solver under human direction. We used problems from Demidovich's calculus collection to identify reusable mathematical rules, implement them, and test the solver on new inputs.

The released solver runs locally without an AI model.

## Development usage

The development logs record 32,514 AI calls and 5,640,661,958 tokens (64,466,997 uncached input, 5,555,276,032 cached input, and 20,918,929 output). The estimated development cost at standard OpenAI API rates was **$3,152.59**. [API pricing](https://developers.openai.com/api/docs/pricing)
