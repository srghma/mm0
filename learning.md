```sh
for i in ../examples/**/*.mm[01]; do mm0-rs compile "$i" &> /dev/null && echo "    $i" || echo "ERR $i"; done

mkdir -p ./from-mm
i="/home/srghma/projects/mm0/simple.mm" && base=$(basename "$i" .mm) && mm0-hs from-mm "$i" -o "from-mm/$base.mm0" "from-mm/$base.mmu"
i="/home/srghma/projects/mm0/linear.mm" && base=$(basename "$i" .mm) && mm0-hs from-mm "$i" -o "from-mm/$base.mm0" "from-mm/$base.mmu"

# nix profile add nixpkgs#metamath
# metamath
# read simple.mm
# verify proof *
# save proof * /compressed
# write source simple-compressed.mm
# exit

i="/home/srghma/projects/mm0/simple-compressed.mm" && base=$(basename "$i" .mm) && mm0-hs from-mm "$i" -o "from-mm/$base.mm0" "from-mm/$base.mmu"

# metamath-lamp https://expln.github.io/lamp/v31/index.html

# pj mm0
# mkdir -p ./from-mm
# for i in /home/srghma/projects/mmj2/data/mm/*.mm; do
#   base=$(basename "$i" .mm)
#   if mm0-hs from-mm "$i" -o "from-mm/$base.mm0" "from-mm/$base.mmu"
#   then
#     echo "    $i"
#   else
#     echo "ERR $i"
#   fi
# done

for i in ../examples/**/*.mm[01]; do mm0-hs from-mm "$i" &> /dev/null && echo "    $i" || echo "ERR $i"; done

mm0-hs to-hol /home/srghma/projects/mm0/from-mm/simple-compressed.mmu -o /home/srghma/projects/mm0/from-mm/simple-compressed.hol
mm0-hs to-lisp /home/srghma/projects/mm0/from-mm/simple-compressed.mmu -o /home/srghma/projects/mm0/from-mm/simple-compressed.lisp
mm0-hs to-othy /home/srghma/projects/mm0/from-mm/simple-compressed.mmu -o /home/srghma/projects/mm0/from-mm/simple-compressed.art
mm0-hs to-lean /home/srghma/projects/mm0/from-mm/simple-compressed.mmu -o /home/srghma/projects/mm0/from-mm/simple-compressed.lean
```
