#!/usr/bin/perl -i
# Perl script that does minor modifications in the SMT scripts that I want to
# submit to the unsat core track.
#
# In the bash shell you can apply this script to all files in the folder using the
# for i in *.smt2 ; do perl THIS_SCRIPT.pl $i; done

while (<>) {
     next if $_ =~ /^\(set-option :produce-models.*\)/;
     next if $_ =~ /^\(set-option :produce-unsat-cores.*\)/;
  if (/^\(check-sat\)/) {
    print $_;
    print "(exit)\n"
  } elsif (/^.*SMT script generated on.*/) {
     print 'SMT script generated by Ultimate Automizer [1,2].
Ultimate Automizer is an automatic software verification tool that implements
a new automata-theoretic approach[3].

This SMT script belongs to a set of SMT scripts that was generated by applying
Ultimate Automizer to benchmarks from the SV-COMP 2015 [4,5] which are available 
at [6].

This script does _not_ contain all SMT commands that are used by Ultimate 
Automizer while verifying a program. In order to fulfill the restrictions of
the main track at SMT-COMP this script contains only the commands that are
sufficient to reproduce one single satisfiablity check.

2015-04-30, Matthias Heizmann (heizmann@informatik.uni-freiburg.de)


[1] https://ultimate.informatik.uni-freiburg.de/automizer/
[2] Matthias Heizmann, Daniel Dietsch, Jan Leike, Betim Musa, Andreas Podelski:
Ultimate Automizer with Array Interpolation - (Competition Contribution). 
TACAS 2015: 455-457
[3] Matthias Heizmann, Jochen Hoenicke, Andreas Podelski: Software Model 
Checking for People Who Love Automata. CAV 2013:36-52
[4] Dirk Beyer: Software Verification and Verifiable Witnesses - (Report on 
SV-COMP 2015). TACAS 2015: 401-416
[5] http://sv-comp.sosy-lab.org/2015/
[6] https://svn.sosy-lab.org/software/sv-benchmarks/tags/svcomp15/
';
  } else {
    print $_;
  }
}
