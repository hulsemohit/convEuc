theory pointreflectionisometry
	imports n3_6a n3_7a n3_7b ABCequalsCBA Geometry Prop03 Prop04 Prop15 betweennotequal congruenceflip congruencesymmetric congruencetransitive differenceofparts doublereverse equalanglesNC equalanglestransitive extensionunique inequalitysymmetric layoffunique lessthancongruence lessthancongruence2 outerconnectivity ray4 ray5 sumofparts
begin

theorem pointreflectionisometry:
	assumes "axioms"
		"midpoint A B C"
		"midpoint P B Q"
	shows "seg_eq A P C Q"
proof -
	have "bet A B C \<and> seg_eq A B B C" using midpoint_f[OF `axioms` `midpoint A B C`] .
	have "bet P B Q \<and> seg_eq P B B Q" using midpoint_f[OF `axioms` `midpoint P B Q`] .
	have "bet A B C" using `bet A B C \<and> seg_eq A B B C` by blast
	have "seg_eq A B B C" using `bet A B C \<and> seg_eq A B B C` by blast
	have "bet P B Q" using `bet P B Q \<and> seg_eq P B B Q` by blast
	have "seg_eq P B B Q" using `bet P B Q \<and> seg_eq P B B Q` by blast
	consider "col A B P"|"\<not> col A B P" by blast
	hence "seg_eq A P C Q"
	proof (cases)
		assume "col A B P"
		have "A = B \<or> A = P \<or> B = P \<or> bet B A P \<or> bet A B P \<or> bet A P B" using collinear_f[OF `axioms` `col A B P`] .
		consider "A = B"|"A = P"|"B = P"|"bet B A P"|"bet A B P"|"bet A P B" using `A = B \<or> A = P \<or> B = P \<or> bet B A P \<or> bet A B P \<or> bet A P B`  by blast
		hence "seg_eq A P C Q"
		proof (cases)
			assume "A = B"
			have "\<not> (\<not> (seg_eq A P C Q))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (seg_eq A P C Q)))"
hence "\<not> (seg_eq A P C Q)" by blast
				have "bet A B C" using midpoint_f[OF `axioms` `midpoint A B C`] by blast
				have "A \<noteq> B" using betweennotequal[OF `axioms` `bet A B C`] by blast
				show "False" using `A \<noteq> B` `A = B` by blast
			qed
			hence "seg_eq A P C Q" by blast
			thus ?thesis by blast
		next
			assume "A = P"
			have "bet P B Q" using `bet P B Q` .
			have "bet A B Q" using `bet P B Q` `A = P` by blast
			have "seg_eq B C A B" using congruencesymmetric[OF `axioms` `seg_eq A B B C`] .
			have "seg_eq A B A B" using congruencereflexiveE[OF `axioms`] .
			have "seg_eq A B P B" using `seg_eq A B A B` `A = P` by blast
			have "seg_eq B C P B" using congruencetransitive[OF `axioms` `seg_eq B C A B` `seg_eq A B P B`] .
			have "seg_eq P B B Q" using `seg_eq P B B Q` .
			have "seg_eq B C B Q" using congruencetransitive[OF `axioms` `seg_eq B C P B` `seg_eq P B B Q`] .
			have "bet A B Q" using `bet A B Q` .
			have "bet A B C" using `bet A B C` .
			have "C = Q" using extensionunique[OF `axioms` `bet A B C` `bet A B Q` `seg_eq B C B Q`] .
			have "seg_eq C Q C Q" using congruencereflexiveE[OF `axioms`] .
			have "seg_eq C Q C C" using `seg_eq C Q C Q` `C = Q` by blast
			have "seg_eq C C C Q" using congruencesymmetric[OF `axioms` `seg_eq C Q C C`] .
			have "seg_eq A P A P" using congruencereflexiveE[OF `axioms`] .
			have "seg_eq A P A A" using `seg_eq A P A P` `A = P` by blast
			have "seg_eq A A C C" using nullsegment2E[OF `axioms`] .
			have "seg_eq A P C C" using congruencetransitive[OF `axioms` `seg_eq A P A A` `seg_eq A A C C`] .
			have "seg_eq A P C Q" using congruencetransitive[OF `axioms` `seg_eq A P C C` `seg_eq C C C Q`] .
			thus ?thesis by blast
		next
			assume "B = P"
			have "\<not> (\<not> (seg_eq A P C Q))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (seg_eq A P C Q)))"
hence "\<not> (seg_eq A P C Q)" by blast
				have "P \<noteq> B" using betweennotequal[OF `axioms` `bet P B Q`] by blast
				have "B \<noteq> P" using inequalitysymmetric[OF `axioms` `P \<noteq> B`] .
				show "False" using `B \<noteq> P` `B = P` by blast
			qed
			hence "seg_eq A P C Q" by blast
			thus ?thesis by blast
		next
			assume "bet B A P"
			have "seg_eq P B B Q" using `seg_eq P B B Q` .
			have "seg_eq A B B C" using `seg_eq A B B C` .
			have "seg_eq B C A B" using congruencesymmetric[OF `axioms` `seg_eq A B B C`] .
			have "seg_eq B C B A" using congruenceflip[OF `axioms` `seg_eq B C A B`] by blast
			have "seg_eq Q B B P" using doublereverse[OF `axioms` `seg_eq P B B Q`] by blast
			have "seg_eq B Q B P" using congruenceflip[OF `axioms` `seg_eq Q B B P`] by blast
			have "seg_eq B A C B" using doublereverse[OF `axioms` `seg_eq A B B C`] by blast
			have "seg_lt C B B P" using lessthan_b[OF `axioms` `bet B A P` `seg_eq B A C B`] .
			have "seg_eq B P B Q" using congruencesymmetric[OF `axioms` `seg_eq B Q B P`] .
			have "seg_lt C B B Q" using lessthancongruence[OF `axioms` `seg_lt C B B P` `seg_eq B P B Q`] .
			have "seg_eq C B B C" using equalityreverseE[OF `axioms`] .
			have "seg_lt B C B Q" using lessthancongruence2[OF `axioms` `seg_lt C B B Q` `seg_eq C B B C`] .
			have "seg_eq B Q B Q" using congruencereflexiveE[OF `axioms`] .
			have "B \<noteq> Q" using betweennotequal[OF `axioms` `bet P B Q`] by blast
			obtain H where "bet B H Q \<and> seg_eq B H B C" using Prop03[OF `axioms` `seg_lt B C B Q` `seg_eq B Q B Q`]  by  blast
			have "bet B H Q" using `bet B H Q \<and> seg_eq B H B C` by blast
			have "seg_eq B H B C" using `bet B H Q \<and> seg_eq B H B C` by blast
			have "ray_on B Q H" using ray4 `axioms` `bet B H Q \<and> seg_eq B H B C` `B \<noteq> Q` by blast
			have "bet P A B" using betweennesssymmetryE[OF `axioms` `bet B A P`] .
			have "bet A B C" using `bet A B C` .
			have "bet P B C" using n3_7a[OF `axioms` `bet P A B` `bet A B C`] .
			have "bet P B Q" using `bet P B Q` .
			have "bet P B C \<and> bet P B Q" using `bet P B C` `bet P B Q \<and> seg_eq P B B Q` by blast
			have "ray_on B C Q" using ray_b[OF `axioms` `bet P B Q` `bet P B C`] .
			have "ray_on B Q C" using ray5[OF `axioms` `ray_on B C Q`] .
			have "seg_eq B C B H" using congruencesymmetric[OF `axioms` `seg_eq B H B C`] .
			have "C = H" using layoffunique[OF `axioms` `ray_on B Q C` `ray_on B Q H` `seg_eq B C B H`] .
			have "bet B C Q" using `bet B H Q` `C = H` by blast
			have "bet B A P" using betweennesssymmetryE[OF `axioms` `bet P A B`] .
			have "seg_eq B A B C" using congruencesymmetric[OF `axioms` `seg_eq B C B A`] .
			have "seg_eq B P B Q" using `seg_eq B P B Q` .
			have "seg_eq A P C Q" using differenceofparts[OF `axioms` `seg_eq B A B C` `seg_eq B P B Q` `bet B A P` `bet B C Q`] .
			thus ?thesis by blast
		next
			assume "bet A B P"
			have "bet P B Q" using `bet P B Q` .
			have "\<not> (\<not> (seg_eq A P C Q))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (seg_eq A P C Q)))"
hence "\<not> (seg_eq A P C Q)" by blast
				have "\<not> (bet B P C)"
				proof (rule ccontr)
					assume "\<not> (\<not> (bet B P C))"
hence "bet B P C" by blast
					have "bet C P B" using betweennesssymmetryE[OF `axioms` `bet B P C`] .
					have "bet C B Q" using n3_7a[OF `axioms` `bet C P B` `bet P B Q`] .
					have "seg_eq A B C B" using congruenceflip[OF `axioms` `seg_eq A B B C`] by blast
					have "seg_eq A B C B" using `seg_eq A B C B` .
					have "seg_eq B P B Q" using congruenceflip[OF `axioms` `seg_eq P B B Q`] by blast
					have "seg_eq A P C Q" using sumofparts[OF `axioms` `seg_eq A B C B` `seg_eq B P B Q` `bet A B P` `bet C B Q`] .
					show "False" using `seg_eq A P C Q` `\<not> (seg_eq A P C Q)` by blast
				qed
				hence "\<not> (bet B P C)" by blast
				have "\<not> (bet B C P)"
				proof (rule ccontr)
					assume "\<not> (\<not> (bet B C P))"
hence "bet B C P" by blast
					have "bet A B P" using n3_7b[OF `axioms` `bet A B C` `bet B C P`] .
					have "bet Q B P" using betweennesssymmetryE[OF `axioms` `bet P B Q`] .
					have "bet Q B C" using innertransitivityE[OF `axioms` `bet Q B P` `bet B C P`] .
					have "bet C B Q" using betweennesssymmetryE[OF `axioms` `bet Q B C`] .
					have "seg_eq A B C B" using congruenceflip[OF `axioms` `seg_eq A B B C`] by blast
					have "seg_eq B P B Q" using congruenceflip[OF `axioms` `seg_eq P B B Q`] by blast
					have "seg_eq A P C Q" using sumofparts[OF `axioms` `seg_eq A B C B` `seg_eq B P B Q` `bet A B P` `bet C B Q`] .
					show "False" using `seg_eq A P C Q` `\<not> (seg_eq A P C Q)` by blast
				qed
				hence "\<not> (bet B C P)" by blast
				have "P = C" using outerconnectivity[OF `axioms` `bet A B P` `bet A B C` `\<not> (bet B P C)` `\<not> (bet B C P)`] .
				have "seg_eq A B B C" using `seg_eq A B B C` .
				have "seg_eq A B B P" using `seg_eq A B B C` `P = C` by blast
				have "seg_eq B P B Q" using congruenceflip[OF `axioms` `seg_eq P B B Q`] by blast
				have "seg_eq A B B Q" using congruencetransitive[OF `axioms` `seg_eq A B B P` `seg_eq B P B Q`] .
				have "bet C B A" using betweennesssymmetryE[OF `axioms` `bet A B C`] .
				have "bet P B A" using `bet C B A` `P = C` by blast
				have "seg_eq B Q A B" using congruencesymmetric[OF `axioms` `seg_eq A B B Q`] .
				have "seg_eq B Q B A" using congruenceflip[OF `axioms` `seg_eq B Q A B`] by blast
				have "Q = A" using extensionunique[OF `axioms` `bet P B Q` `bet P B A` `seg_eq B Q B A`] .
				have "seg_eq A C C A" using equalityreverseE[OF `axioms`] .
				have "seg_eq A P C A" using `seg_eq A C C A` `P = C` by blast
				have "seg_eq A P C Q" using `seg_eq A C C A` `P = C` `Q = A` by blast
				show "False" using `seg_eq A P C Q` `\<not> (seg_eq A P C Q)` by blast
			qed
			hence "seg_eq A P C Q" by blast
			thus ?thesis by blast
		next
			assume "bet A P B"
			have "seg_eq A B B C" using `seg_eq A B B C` .
			have "seg_eq P B B Q" using `seg_eq P B B Q` .
			have "seg_eq B Q P B" using congruencesymmetric[OF `axioms` `seg_eq P B B Q`] .
			have "seg_eq B Q B P" using congruenceflip[OF `axioms` `seg_eq B Q P B`] by blast
			have "seg_eq C B B A" using doublereverse[OF `axioms` `seg_eq A B B C`] by blast
			have "seg_eq B C B A" using congruenceflip[OF `axioms` `seg_eq C B B A`] by blast
			have "bet B P A" using betweennesssymmetryE[OF `axioms` `bet A P B`] .
			have "seg_eq B P Q B" using doublereverse[OF `axioms` `seg_eq B Q P B`] by blast
			have "seg_lt Q B B A" using lessthan_b[OF `axioms` `bet B P A` `seg_eq B P Q B`] .
			have "seg_eq B A B C" using congruencesymmetric[OF `axioms` `seg_eq B C B A`] .
			have "seg_lt Q B B C" using lessthancongruence[OF `axioms` `seg_lt Q B B A` `seg_eq B A B C`] .
			have "seg_eq Q B B Q" using equalityreverseE[OF `axioms`] .
			have "seg_lt B Q B C" using lessthancongruence2[OF `axioms` `seg_lt Q B B C` `seg_eq Q B B Q`] .
			have "seg_eq B C B C" using congruencereflexiveE[OF `axioms`] .
			have "B \<noteq> C" using betweennotequal[OF `axioms` `bet A B C`] by blast
			obtain H where "bet B H C \<and> seg_eq B H B Q" using Prop03[OF `axioms` `seg_lt B Q B C` `seg_eq B C B C`]  by  blast
			have "bet B H C" using `bet B H C \<and> seg_eq B H B Q` by blast
			have "seg_eq B H B Q" using `bet B H C \<and> seg_eq B H B Q` by blast
			have "bet A B C" using `bet A B C` .
			have "bet P B C" using n3_6a[OF `axioms` `bet A P B` `bet A B C`] .
			have "bet P B Q" using `bet P B Q` .
			have "bet P B C \<and> bet P B Q" using `bet P B C` `bet P B Q \<and> seg_eq P B B Q` by blast
			have "ray_on B C Q" using ray_b[OF `axioms` `bet P B Q` `bet P B C`] .
			have "ray_on B C H" using ray4 `axioms` `bet B H C \<and> seg_eq B H B Q` `B \<noteq> C` by blast
			have "seg_eq B Q B H" using congruencesymmetric[OF `axioms` `seg_eq B H B Q`] .
			have "Q = H" using layoffunique[OF `axioms` `ray_on B C Q` `ray_on B C H` `seg_eq B Q B H`] .
			have "bet B Q C" using `bet B H C` `Q = H` by blast
			have "bet B P A" using betweennesssymmetryE[OF `axioms` `bet A P B`] .
			have "seg_eq B P B Q" using congruencesymmetric[OF `axioms` `seg_eq B Q B P`] .
			have "seg_eq B A B C" using `seg_eq B A B C` .
			have "seg_eq P A Q C" using differenceofparts[OF `axioms` `seg_eq B P B Q` `seg_eq B A B C` `bet B P A` `bet B Q C`] .
			have "seg_eq A P C Q" using congruenceflip[OF `axioms` `seg_eq P A Q C`] by blast
			thus ?thesis by blast
		qed
		thus ?thesis by blast
	next
		assume "\<not> col A B P"
		have "ang_eq A B P Q B C" using Prop15[OF `axioms` `bet A B C` `bet P B Q` `\<not> col A B P`] by blast
		have "\<not> col Q B C" using equalanglesNC[OF `axioms` `ang_eq A B P Q B C`] .
		have "ang_eq Q B C C B Q" using ABCequalsCBA[OF `axioms` `\<not> col Q B C`] .
		have "ang_eq A B P C B Q" using equalanglestransitive[OF `axioms` `ang_eq A B P Q B C` `ang_eq Q B C C B Q`] .
		have "seg_eq B A B C" using congruenceflip[OF `axioms` `seg_eq A B B C`] by blast
		have "seg_eq B P B Q" using congruenceflip[OF `axioms` `seg_eq P B B Q`] by blast
		have "seg_eq A P C Q" using Prop04[OF `axioms` `seg_eq B A B C` `seg_eq B P B Q` `ang_eq A B P C B Q`] by blast
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end