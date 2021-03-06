theory rightreflection
	imports Geometry betweennesspreserved congruenceflip congruencesymmetric congruencetransitive doublereverse nullsegment3 pointreflectionisometry
begin

theorem(in euclidean_geometry) rightreflection:
	assumes 
		"ang_right A B C"
		"midpoint A E a"
		"midpoint B E b"
		"midpoint C E c"
	shows "ang_right a b c"
proof -
	obtain D where "bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C" using rightangle_f[OF `ang_right A B C`]  by  blast
	have "B \<noteq> C" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	have "seg_eq A B a b" using pointreflectionisometry[OF `midpoint A E a` `midpoint B E b`] .
	have "seg_eq A C a c" using pointreflectionisometry[OF `midpoint A E a` `midpoint C E c`] .
	have "seg_eq B C b c" using pointreflectionisometry[OF `midpoint B E b` `midpoint C E c`] .
	consider "D = E"|"D \<noteq> E" by blast
	hence "ang_right a b c"
	proof (cases)
		assume "D = E"
		have "seg_eq B E E b" using midpoint_f[OF `midpoint B E b`] by blast
		have "seg_eq C E E c" using midpoint_f[OF `midpoint C E c`] by blast
		have "bet A B D" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
		have "seg_eq A B a b" using `seg_eq A B a b` .
		have "seg_eq A E E a" using midpoint_f[OF `midpoint A E a`] by blast
		have "seg_eq A D D a" using `seg_eq A E E a` `D = E` `D = E` by blast
		have "seg_eq A D a D" using congruenceflip[OF `seg_eq A D D a`] by blast
		have "seg_eq B E E b" using midpoint_f[OF `midpoint B E b`] by blast
		have "seg_eq B D D b" using `seg_eq B E E b` `D = E` `D = E` by blast
		have "seg_eq B D b D" using congruenceflip[OF `seg_eq B D D b`] by blast
		have "seg_eq D B D b" using congruenceflip[OF `seg_eq B D D b`] by blast
		have "bet a b D" using betweennesspreserved[OF `seg_eq A B a b` `seg_eq A D a D` `seg_eq B D b D` `bet A B D`] .
		have "seg_eq a b A B" using congruencesymmetric[OF `seg_eq A B a b`] .
		have "seg_eq A B D B" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
		have "seg_eq a b D B" using congruencetransitive[OF `seg_eq a b A B` `seg_eq A B D B`] .
		have "seg_eq a b D b" using congruencetransitive[OF `seg_eq a b D B` `seg_eq D B D b`] .
		have "seg_eq a c A C" using congruencesymmetric[OF `seg_eq A C a c`] .
		have "seg_eq A C D C" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
		have "seg_eq a c D C" using congruencetransitive[OF `seg_eq a c A C` `seg_eq A C D C`] .
		have "seg_eq C E E c" using midpoint_f[OF `midpoint C E c`] by blast
		have "seg_eq C D D c" using `seg_eq C E E c` `D = E` `D = E` by blast
		have "seg_eq D C D c" using congruenceflip[OF `seg_eq C D D c`] by blast
		have "seg_eq a c D c" using congruencetransitive[OF `seg_eq a c D C` `seg_eq D C D c`] .
		have "b \<noteq> c" using nullsegment3[OF `B \<noteq> C` `seg_eq B C b c`] .
		have "ang_right a b c" using rightangle_b[OF `bet a b D` `seg_eq a b D b` `seg_eq a c D c` `b \<noteq> c`] .
		thus ?thesis by blast
	next
		assume "D \<noteq> E"
		obtain d where "bet D E d \<and> seg_eq E d D E" using extensionE[OF `D \<noteq> E` `D \<noteq> E`]  by  blast
		have "bet D E d" using `bet D E d \<and> seg_eq E d D E` by blast
		have "seg_eq E d D E" using `bet D E d \<and> seg_eq E d D E` by blast
		have "seg_eq E D d E" using doublereverse[OF `seg_eq E d D E`] by blast
		have "seg_eq D E E d" using congruenceflip[OF `seg_eq E D d E`] by blast
		have "midpoint D E d" using midpoint_b[OF `bet D E d` `seg_eq D E E d`] .
		have "seg_eq B D b d" using pointreflectionisometry[OF `midpoint B E b` `midpoint D E d`] .
		have "seg_eq D C d c" using pointreflectionisometry[OF `midpoint D E d` `midpoint C E c`] .
		have "seg_eq a c A C" using congruencesymmetric[OF `seg_eq A C a c`] .
		have "seg_eq A C D C" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
		have "seg_eq a c D C" using congruencetransitive[OF `seg_eq a c A C` `seg_eq A C D C`] .
		have "seg_eq a c d c" using congruencetransitive[OF `seg_eq a c D C` `seg_eq D C d c`] .
		have "b \<noteq> c" using nullsegment3[OF `B \<noteq> C` `seg_eq B C b c`] .
		have "bet A B D" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
		have "seg_eq A B a b" using `seg_eq A B a b` .
		have "seg_eq A D a d" using pointreflectionisometry[OF `midpoint A E a` `midpoint D E d`] .
		have "seg_eq B D b d" using `seg_eq B D b d` .
		have "bet a b d" using betweennesspreserved[OF `seg_eq A B a b` `seg_eq A D a d` `seg_eq B D b d` `bet A B D`] .
		have "seg_eq a b A B" using congruencesymmetric[OF `seg_eq A B a b`] .
		have "seg_eq A B D B" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
		have "seg_eq a b D B" using congruencetransitive[OF `seg_eq a b A B` `seg_eq A B D B`] .
		have "seg_eq D B d b" using pointreflectionisometry[OF `midpoint D E d` `midpoint B E b`] .
		have "seg_eq a b d b" using congruencetransitive[OF `seg_eq a b D B` `seg_eq D B d b`] .
		have "seg_eq a c d c" using `seg_eq a c d c` .
		have "b \<noteq> c" using `b \<noteq> c` .
		have "ang_right a b c" using rightangle_b[OF `bet a b d` `seg_eq a b d b` `seg_eq a c d c` `b \<noteq> c`] .
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end