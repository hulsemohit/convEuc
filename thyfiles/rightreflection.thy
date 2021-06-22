theory rightreflection
	imports Axioms Definitions Theorems
begin

theorem rightreflection:
	assumes: `axioms`
		"ang_right A B C"
		"midpoint A E a"
		"midpoint B E b"
		"midpoint C E c"
	shows: "ang_right a b c"
proof -
	obtain D where "bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C" sorry
	have "B \<noteq> C" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	have "seg_eq A B a b" using pointreflectionisometry[OF `axioms` `midpoint A E a` `midpoint B E b`] .
	have "seg_eq A C a c" using pointreflectionisometry[OF `axioms` `midpoint A E a` `midpoint C E c`] .
	have "seg_eq B C b c" using pointreflectionisometry[OF `axioms` `midpoint B E b` `midpoint C E c`] .
	consider "D = E"|"D \<noteq> E" by blast
	hence ang_right a b c
	proof (cases)
		case 1
		have "seg_eq B E E b" sorry
		have "seg_eq C E E c" sorry
		have "bet A B D" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
		have "seg_eq A B a b" using `seg_eq A B a b` .
		have "seg_eq A E E a" sorry
		have "seg_eq A D D a" sorry
		have "seg_eq A D a D" using congruenceflip[OF `axioms` `seg_eq A D D a`] by blast
		have "seg_eq B E E b" sorry
		have "seg_eq B D D b" sorry
		have "seg_eq B D b D" using congruenceflip[OF `axioms` `seg_eq B D D b`] by blast
		have "seg_eq D B D b" using congruenceflip[OF `axioms` `seg_eq B D D b`] by blast
		have "bet a b D" using betweennesspreserved[OF `axioms` `seg_eq A B a b` `seg_eq A D a D` `seg_eq B D b D` `bet A B D`] .
		have "seg_eq a b A B" using congruencesymmetric[OF `axioms` `seg_eq A B a b`] .
		have "seg_eq A B D B" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
		have "seg_eq a b D B" using congruencetransitive[OF `axioms` `seg_eq a b A B` `seg_eq A B D B`] .
		have "seg_eq a b D b" using congruencetransitive[OF `axioms` `seg_eq a b D B` `seg_eq D B D b`] .
		have "seg_eq a c A C" using congruencesymmetric[OF `axioms` `seg_eq A C a c`] .
		have "seg_eq A C D C" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
		have "seg_eq a c D C" using congruencetransitive[OF `axioms` `seg_eq a c A C` `seg_eq A C D C`] .
		have "seg_eq C E E c" sorry
		have "seg_eq C D D c" sorry
		have "seg_eq D C D c" using congruenceflip[OF `axioms` `seg_eq C D D c`] by blast
		have "seg_eq a c D c" using congruencetransitive[OF `axioms` `seg_eq a c D C` `seg_eq D C D c`] .
		have "b \<noteq> c" using nullsegment3[OF `axioms` `B \<noteq> C` `seg_eq B C b c`] .
		have "ang_right a b c" sorry
	next
		case 2
		obtain d where "bet D E d \<and> seg_eq E d D E" using extensionE[OF `axioms` `D \<noteq> E` `D \<noteq> E`]  by  blast
		have "bet D E d" using `bet D E d \<and> seg_eq E d D E` by blast
		have "seg_eq E d D E" using `bet D E d \<and> seg_eq E d D E` by blast
		have "seg_eq E D d E" using doublereverse[OF `axioms` `seg_eq E d D E`] by blast
		have "seg_eq D E E d" using congruenceflip[OF `axioms` `seg_eq E D d E`] by blast
		have "midpoint D E d" sorry
		have "seg_eq B D b d" using pointreflectionisometry[OF `axioms` `midpoint B E b` `midpoint D E d`] .
		have "seg_eq D C d c" using pointreflectionisometry[OF `axioms` `midpoint D E d` `midpoint C E c`] .
		have "seg_eq a c A C" using congruencesymmetric[OF `axioms` `seg_eq A C a c`] .
		have "seg_eq A C D C" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
		have "seg_eq a c D C" using congruencetransitive[OF `axioms` `seg_eq a c A C` `seg_eq A C D C`] .
		have "seg_eq a c d c" using congruencetransitive[OF `axioms` `seg_eq a c D C` `seg_eq D C d c`] .
		have "b \<noteq> c" using nullsegment3[OF `axioms` `B \<noteq> C` `seg_eq B C b c`] .
		have "bet A B D" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
		have "seg_eq A B a b" using `seg_eq A B a b` .
		have "seg_eq A D a d" using pointreflectionisometry[OF `axioms` `midpoint A E a` `midpoint D E d`] .
		have "seg_eq B D b d" using `seg_eq B D b d` .
		have "bet a b d" using betweennesspreserved[OF `axioms` `seg_eq A B a b` `seg_eq A D a d` `seg_eq B D b d` `bet A B D`] .
		have "seg_eq a b A B" using congruencesymmetric[OF `axioms` `seg_eq A B a b`] .
		have "seg_eq A B D B" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
		have "seg_eq a b D B" using congruencetransitive[OF `axioms` `seg_eq a b A B` `seg_eq A B D B`] .
		have "seg_eq D B d b" using pointreflectionisometry[OF `axioms` `midpoint D E d` `midpoint B E b`] .
		have "seg_eq a b d b" using congruencetransitive[OF `axioms` `seg_eq a b D B` `seg_eq D B d b`] .
		have "seg_eq a c d c" using `seg_eq a c d c` .
		have "b \<noteq> c" using `b \<noteq> c` .
		have "ang_right a b c" sorry
	next
	thus ?thesis by blast
qed

end