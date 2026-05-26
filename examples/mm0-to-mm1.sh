#!/bin/sh

# Detect where mm0-rs is located (PATH or release target)
if [ -f "./mm0-rs/target/release/mm0-rs" ]; then
  MM0_RS="./mm0-rs/target/release/mm0-rs"
elif command -v mm0-rs &> /dev/null; then
  MM0_RS=mm0-rs
else
  echo "Error: mm0-rs executable not found in PATH or ./mm0-rs/target/release/"
  exit 1
fi

# Recursively update mm0 files from mm1 files in examples/
for i in ./examples/*.mm1; do
  echo "Updating ${i%.mm1}.mm0..."
  "$MM0_RS" mm1-to-mm0 "$i" "${i%.mm1}.mm0" --no-inline-imports
done

echo "Running compilation checks..."
# Run compile like for i in ./examples/*.mm[01]; do mm0-rs compile "$i" &> /dev/null && echo "    $i" || echo "ERR $i"; done
for i in ./examples/*.mm[01]; do
  "$MM0_RS" compile "$i" &> /dev/null && echo "    $i" || echo "ERR $i"
done
