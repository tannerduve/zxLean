# Theoros

[https://en.wiktionary.org/wiki/θεωρός](https://en.wiktionary.org/wiki/θεωρός#:~:text=Noun[edit]θεωρός%20•%20(theōrós)%C2%A0m%20(genitive%20θεωροῦ);%20second%20declensionspectatorenvoy%20sent%20to%20consult%20an%20oracle).

A wrapper over [Harmonic's](https://harmonic.fun) Aristotle API to make proving theorems in Lean easier.

```bash
curl -LsSf https://astral.sh/uv/install.sh | sh # If you don't have uv installed already
export ARISTOTLE_API_KEY="your-api-key-here"

cd py
uv run theoros.py prove ../ZxCalculus/<FILE_NAME>.lean
```

## Usage

### Proving Theorems

```bash
cd py

# Prove a file (output and logs go to logs/ directory)
uv run theoros.py prove ../ZxCalculus/YourFile.lean

# Specify custom output location
uv run theoros.py prove ../ZxCalculus/File.lean --output proved.lean

# Use different logs directory
uv run theoros.py prove ../ZxCalculus/File.lean --logs-dir my_logs

# Disable progress bar
uv run theoros.py prove ../ZxCalculus/File.lean --no-progress

# Provide API key via command line
uv run theoros.py prove ../ZxCalculus/File.lean --api-key YOUR_KEY
```

### Reviewing Logs

```bash
# List all proof logs
uv run theoros.py review --list

# View diff in interactive pager (keyboard navigation only: arrows/Page Up/Down, 'q' to quit)
uv run theoros.py review --file logs/proof_MatrixLemmas_20251113_110633.txt

# View diff without pager (prints directly to terminal)
uv run theoros.py review --file logs/proof_MatrixLemmas_20251113_110633.txt --no-pager

# Export log to JSON for analysis (can combine with diff viewing)
uv run theoros.py review --file logs/proof_MatrixLemmas_20251113_110633.txt --export-json data.json

# Show table of all logs (same as --list)
uv run theoros.py review
```


