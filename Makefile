# ConstructiveWorld-Main build entry Makefile (trust-cache incremental build; legacy merged recipe retained as retired)
#
# Usage:
#   make modules   # compile the registered modules in the topological order of scripts/order.txt (skips modules whose .vo already exists)
#   make check     # full-tree coqchk kernel re-verification (shared closure passed in a single batch; certification scale follows the current trust cache)
#   make merged    # (retired) legacy single-file merged build recipe of the 220 era, kept under releases/ for historical reproduction (see the README appendix);
#                  #  not part of the active certification surface; for routine verification use modules + check
#   make clean     # remove build artifacts (.v sources kept)
#
# Variable overrides (Windows local example):
#   make COQC="C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe" COQCHK="C:/Rocq-Platform~9.1~2026.01/bin/coqchk.exe"

COQC   ?= coqc
COQCHK ?= coqchk
ORDER  := scripts/order.txt
VODIR  := ConstructiveWorld_vo

modules:
	cd $(VODIR) && bash build.sh

check:
	cd $(VODIR) && bash coqchk_all.sh

# (retired) legacy 220 merged build recipe: the target file is releases/CW_ConstructiveWorld_220.v (kept as a historical record).
# The active build and certification surface is the modules / check targets above.
merged:
	cd $(VODIR) && $(COQC) -Q . "" CW_ConstructiveWorld_220.v || \
	cd ../releases && $(COQC) -Q . "" CW_ConstructiveWorld_220.v

clean:
	cd $(VODIR) && rm -f *.vo *.vos *.vok *.glob _*.build.log _chk_*.log

.PHONY: modules check merged clean
