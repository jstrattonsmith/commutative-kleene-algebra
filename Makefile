# Default target
all: RocqMakefile
	+@$(MAKE) -f RocqMakefile all
.PHONY: all

# Permit local customization
-include Makefile.local

# Forward most targets to Rocq makefile (with some trick to make this phony)
%: RocqMakefile phony
	@#echo "Forwarding $@"
	+@$(MAKE) -f RocqMakefile $@
phony: ;
.PHONY: phony

clean: RocqMakefile
	+@$(MAKE) -f RocqMakefile clean
	find . -maxdepth 1 \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete || true
	rm -f RocqMakefile* .lia.cache
.PHONY: clean

# Create Rocq Makefile.
RocqMakefile: _CoqProject Makefile
	"$(COQBIN)coq_makefile" -f _CoqProject -o RocqMakefile $(EXTRA_COQFILES)

# Some files that do *not* need to be forwarded to RocqMakefile.
# ("::" lets Makefile.local overwrite this.)
Makefile Makefile.local _CoqProject:: ;
