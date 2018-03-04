## Make rules for subdirectories

# The including Makefile is expected to set the following variables:
#
#	FILES		List of coq source files
#
# Additionally, the user may set the following variables:
#
# 	CROSSDEP	warn|ignore|rebuild
#

# Figure out where we are
TOPDIR= $(dir $(CURDIR))
SUBDIR= $(notdir $(CURDIR))

# Set the COQPATH environment variable to the top-level directory
COQPATH= $(TOPDIR)
export COQPATH

# Default values for parameters
CROSSDEP = warn
# TIMELOG = .timelog

# Toolchain
COQC= coqc
COQTOP= coqtop
COQDOC= coqdoc
OCAMLBUILD= ocamlbuild

# Hookable targets: subdir Makefiles can extend them by adding dependencies.
all: all-vo
clean: clean-vo


## Compiling Coq sources files

# Compile all of them
all-vo: $(FILES:.v=.vo)

# Compile one of them
ifeq ($(TIMELOG),)
%.vo: %.v
#	$(COQC) $*
	@echo $(COQC) $*
	@(printf $* && printf " " && (/usr/bin/time -p $(COQC) $*)) > $@.time 2>&1
	@cat $@.time >> timelog
	@$(RM) $@.time
else
# Keep a log of compilation times: if $(TIMELOG) is defined,
# we write an entry there each time we build a .vo file.
GITREV := $(shell git rev-parse --short HEAD)
GITMOD := $(shell git status --porcelain --untracked=no | grep -q . && echo +)
TIME = /usr/bin/time -o $@.time -f "$(GITREV)$(GITMOD):$(SUBDIR)/$< %U %S %E %P"
%.vo: %.v
	@echo $(COQC) $*
	@$(TIME) -o $@.time $(COQC) $*
	@cat $@.time >> ../$(TIMELOG)
	@$(RM) $@.time
endif

# Cleanup
clean-vo:
	$(RM) $(FILES:.v=.vo) $(FILES:.v=.glob) $(FILES:.v=.vo.time)


## Out-of-date files in other subdirectories

# The way we handle out-of-date files from other subdirectories depend on the
# value of the variables $(CROSSDEP). If it is 'ignore', then we do nothing.
# If it is 'warn' (the default), we emit a warning but do not try to rebuild
# them either. If it is 'build', then we attempt to rebuild it as if it were
# one of our files.

ifeq ($(CROSSDEP),ignore)
../%.vo:

else
ifneq ($(CROSSDEP),build)
../%.vo:
	@echo "W: $@ seems out of date, you may want to rebuild"
endif
endif


## Dependency handling

# Print a list of all our .v files
.PHONY: listfiles
listfiles:
	for f in $(FILES); do \
	  echo $$f; \
	done

# The top-level Makefile will use the previous rule to build a global .depend
# file. We specialize the global .depend for our specific subdirectory.
.depend: ../.depend
	sed 's_../$(SUBDIR)/__g' $< >$@.n
	mv $@.n $@

# If it exists, load the result.
-include .depend


## Documentation

.PHONY: documentation
documentation: html
clean: clean-html

# FIXME: we may want a global thing instead of a per-directory one, so that
# hyperlinks can take us anywhere and there is one complete set of HTML files.
html: $(FILES:.v=.vo)
	$(RM) -r $@.n
	mkdir $@.n
	$(COQDOC) -R . $(SUBDIR) --html -d $@.n --toc --utf8 $(FILES)
	$(RM) -r $@
	mv $@.n $@

.PHONY: clean-html
clean-html:
	$(RM) -r html

