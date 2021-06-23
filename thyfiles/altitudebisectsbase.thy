theory altitudebisectsbase
	imports n8_2 n8_3 Geometry Prop04 betweennotequal collinearorder congruenceflip congruencesymmetric congruencetransitive doublereverse extensionunique inequalitysymmetric ray4 rightangleNC
begin

theorem altitudebisectsbase:
	assumes "axioms"
		"bet A M B"
		"seg_eq A P B P"
		"ang_right A M P"
	shows "midpoint A M B"
proof -
	obtain C where "bet A M C \<and> seg_eq A M C M \<and> seg_eq A P C P \<and> M \<noteq> P" using rightangle_f[OF `axioms` `ang_right A M P`]  by  blast
	have "bet A M C" using `bet A M C \<and> seg_eq A M C M \<and> seg_eq A P C P \<and> M \<noteq> P` by blast
	have "seg_eq A M C M" using `bet A M C \<and> seg_eq A M C M \<and> seg_eq A P C P \<and> M \<noteq> P` by blast
	have "seg_eq A P C P" using `bet A M C \<and> seg_eq A M C M \<and> seg_eq A P C P \<and> M \<noteq> P` by blast
	have "M \<noteq> P" using `bet A M C \<and> seg_eq A M C M \<and> seg_eq A P C P \<and> M \<noteq> P` by blast
	have "bet C M A" using betweennesssymmetryE[OF `axioms` `bet A M C`] .
	have "seg_eq C M A M" using congruencesymmetric[OF `axioms` `seg_eq A M C M`] .
	have "seg_eq C P A P" using congruencesymmetric[OF `axioms` `seg_eq A P C P`] .
	have "ang_right C M P" using rightangle_b[OF `axioms` `bet C M A` `seg_eq C M A M` `seg_eq C P A P` `M \<noteq> P`] .
	have "ang_right P M A" using n8_2[OF `axioms` `ang_right A M P`] .
	obtain Q where "bet P M Q \<and> seg_eq P M Q M \<and> seg_eq P A Q A \<and> M \<noteq> A" using rightangle_f[OF `axioms` `ang_right P M A`]  by  blast
	have "seg_eq P M Q M" using `bet P M Q \<and> seg_eq P M Q M \<and> seg_eq P A Q A \<and> M \<noteq> A` by blast
	have "seg_eq P A Q A" using `bet P M Q \<and> seg_eq P M Q M \<and> seg_eq P A Q A \<and> M \<noteq> A` by blast
	have "seg_eq Q M P M" using congruencesymmetric[OF `axioms` `seg_eq P M Q M`] .
	have "seg_eq Q M P M" using `seg_eq Q M P M` .
	have "ang_right P M C" using n8_2[OF `axioms` `ang_right C M P`] .
	have "ray_on M C B" using ray_b[OF `axioms` `bet A M B` `bet A M C`] .
	have "ang_right P M B" using n8_3[OF `axioms` `ang_right P M C` `ray_on M C B`] .
	obtain E where "bet P M E \<and> seg_eq P M E M \<and> seg_eq P B E B \<and> M \<noteq> B" using rightangle_f[OF `axioms` `ang_right P M B`]  by  blast
	have "seg_eq P M E M" using `bet P M E \<and> seg_eq P M E M \<and> seg_eq P B E B \<and> M \<noteq> B` by blast
	have "seg_eq P B E B" using `bet P M E \<and> seg_eq P M E M \<and> seg_eq P B E B \<and> M \<noteq> B` by blast
	have "seg_eq P A P B" using congruenceflip[OF `axioms` `seg_eq A P B P`] by blast
	have "bet P M E" using `bet P M E \<and> seg_eq P M E M \<and> seg_eq P B E B \<and> M \<noteq> B` by blast
	have "bet P M Q" using `bet P M Q \<and> seg_eq P M Q M \<and> seg_eq P A Q A \<and> M \<noteq> A` by blast
	have "seg_eq M Q P M" using congruenceflip[OF `axioms` `seg_eq Q M P M`] by blast
	have "seg_eq P M M Q" using congruencesymmetric[OF `axioms` `seg_eq M Q P M`] .
	have "seg_eq E M P M" using congruencesymmetric[OF `axioms` `seg_eq P M E M`] .
	have "seg_eq E M M Q" using congruencetransitive[OF `axioms` `seg_eq E M P M` `seg_eq P M M Q`] .
	have "seg_eq M E M Q" using congruenceflip[OF `axioms` `seg_eq E M M Q`] by blast
	have "seg_eq M Q M E" using congruencesymmetric[OF `axioms` `seg_eq M E M Q`] .
	have "P \<noteq> M" using betweennotequal[OF `axioms` `bet P M E`] by blast
	have "Q = E" using extensionunique[OF `axioms` `bet P M Q` `bet P M E` `seg_eq M Q M E`] .
	have "seg_eq P B Q B" using `seg_eq P B E B` `Q = E` by blast
	have "seg_eq A P P B" using congruenceflip[OF `axioms` `seg_eq A P B P`] by blast
	have "seg_eq A P Q B" using congruencetransitive[OF `axioms` `seg_eq A P P B` `seg_eq P B Q B`] .
	have "seg_eq A Q A P" using doublereverse[OF `axioms` `seg_eq P A Q A`] by blast
	have "seg_eq A Q Q B" using congruencetransitive[OF `axioms` `seg_eq A Q A P` `seg_eq A P Q B`] .
	have "seg_eq A Q B Q" using congruenceflip[OF `axioms` `seg_eq A Q Q B`] by blast
	have "seg_eq P Q P Q" using congruencereflexiveE[OF `axioms`] .
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "\<not> col A M P" using rightangleNC[OF `axioms` `ang_right A M P`] .
	have "\<not> (col A P M)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A P M))"
hence "col A P M" by blast
		have "col A M P" using collinearorder[OF `axioms` `col A P M`] by blast
		show "False" using `col A M P` `\<not> col A M P` by blast
	qed
	hence "\<not> col A P M" by blast
	have "\<not> (A = P)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> P)"
		hence "A = P" by blast
		have "col A P M" using collinear_b `axioms` `A = P` by blast
		show "False" using `col A P M` `\<not> col A P M` by blast
	qed
	hence "A \<noteq> P" by blast
	have "P \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> P`] .
	have "ray_on P A A" using ray4 `axioms` `A = A` `P \<noteq> A` by blast
	have "\<not> (P = B)"
	proof (rule ccontr)
		assume "\<not> (P \<noteq> B)"
		hence "P = B" by blast
		have "seg_eq A P B P" using `seg_eq A P B P` .
		have "seg_eq A P B B" using `seg_eq A P B P` `P = B` by blast
		have "A = P" using nullsegment1E[OF `axioms` `seg_eq A P B B`] .
		show "False" using `A = P` `A \<noteq> P` by blast
	qed
	hence "P \<noteq> B" by blast
	have "ray_on P B B" using ray4 `axioms` `B = B` `P \<noteq> B` by blast
	have "bet P M Q" using `bet P M Q` .
	have "ray_on P M Q" using ray4 `axioms` `bet P M Q \<and> seg_eq P M Q M \<and> seg_eq P A Q A \<and> M \<noteq> A` `P \<noteq> M` by blast
	have "ray_on P A A \<and> ray_on P B B \<and> ray_on P M Q \<and> ray_on P M Q \<and> seg_eq P A P B \<and> seg_eq P Q P Q \<and> seg_eq A Q B Q \<and> \<not> col A P M" using `ray_on P A A` `ray_on P B B` `ray_on P M Q` `ray_on P M Q` `seg_eq P A P B` `seg_eq P Q P Q` `seg_eq A Q B Q` `\<not> col A P M` by blast
	have "ang_eq A P M B P M" using equalangles_b[OF `axioms` `ray_on P A A` `ray_on P M Q` `ray_on P B B` `ray_on P M Q` `seg_eq P A P B` `seg_eq P Q P Q` `seg_eq A Q B Q` `\<not> col A P M`] .
	have "seg_eq P M P M" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq A M B M \<and> ang_eq P A M P B M \<and> ang_eq P M A P M B" using Prop04[OF `axioms` `seg_eq P A P B` `seg_eq P M P M` `ang_eq A P M B P M`] .
	have "seg_eq A M B M" using `seg_eq A M B M \<and> ang_eq P A M P B M \<and> ang_eq P M A P M B` by blast
	have "seg_eq A M M B" using congruenceflip[OF `axioms` `seg_eq A M B M`] by blast
	have "bet A M B \<and> seg_eq A M M B" using `bet A M B` `seg_eq A M M B` by blast
	have "midpoint A M B" using midpoint_b[OF `axioms` `bet A M B` `seg_eq A M M B`] .
	thus ?thesis by blast
qed

end