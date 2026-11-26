# Math Chain Solver

A local symbolic solver with a replayable reasoning chain. Runs with Python 3.12 and the standard library. No build step, API keys, or network access are required.

Run from this directory:

    python -B -X utf8 run.py solve "sin(3*x)/x" --side both --out demo
    python -B -X utf8 run.py replay demo/run.json

The explanation is in demo/run.txt. Use python run.py --help for other commands.

For a custom task, save a UTF-8 JSON array as tasks.json. For example:

    [{"id":"nth-derivative","kind":"symbolic_order_derivative","function":"cos(3*t+1)*exp(2*t)","variable":"t","order":"n"}]

Then run:

    python -B -X utf8 run.py batch tasks.json --out demo-batch
    python -B -X utf8 run.py replay demo-batch/nth-derivative.json

The bundle includes snapshot v157 and 329 executable rules. Some tasks remain unresolved.

## How it was built

AI agents developed this solver under human direction. We used problems from Demidovich's calculus collection to identify reusable mathematical rules, implement them, and test the solver on new inputs.

The released solver runs locally without an AI model.
