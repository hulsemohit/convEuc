theory lessthancongruence
	imports Geometry betweennesspreserved betweennotequal congruencesymmetric congruencetransitive doublereverse equalitysymmetric inequalitysymmetric nullsegment3 sumofparts
begin

theorem lessthancongruence:
	assumes "axioms"
		"seg_lt A B C D"
		"seg_eq C D E F"
	shows "seg_lt A B E F"
proof -
	obtain G where "bet C G D \<and> seg_eq C G A B" using lessthan_f[OF `axioms` `seg_lt A B C D`]  by  blast
	have "bet C G D" using `bet C G D \<and> seg_eq C G A B` by blast
	have "seg_eq C G A B" using `bet C G D \<and> seg_eq C G A B` by blast
	have "C \<noteq> D" using betweennotequal[OF `axioms` `bet C G D`] by blast
	have "E \<noteq> F" using nullsegment3[OF `axioms` `C \<noteq> D` `seg_eq C D E F`] .
	have "\<not> (F = E)"
	proof (rule ccontr)
		assume "\<not> (F \<noteq> E)"
		hence "F = E" by blast
		have "E = F" using equalitysymmetric[OF `axioms` `F = E`] .
		show "False" using `E = F` `E \<noteq> F` by blast
	qed
	hence "F \<noteq> E" by blast
	obtain P where "bet F E P \<and> seg_eq E P F E" using extensionE[OF `axioms` `F \<noteq> E` `F \<noteq> E`]  by  blast
	have "bet F E P" using `bet F E P \<and> seg_eq E P F E` by blast
	have "bet P E F" using betweennesssymmetryE[OF `axioms` `bet F E P`] .
	have "P \<noteq> E" using betweennotequal[OF `axioms` `bet P E F`] by blast
	have "C \<noteq> G" using betweennotequal[OF `axioms` `bet C G D`] by blast
	have "A \<noteq> B" using nullsegment3[OF `axioms` `C \<noteq> G` `seg_eq C G A B`] .
	obtain H where "bet P E H \<and> seg_eq E H A B" using extensionE[OF `axioms` `P \<noteq> E` `A \<noteq> B`]  by  blast
	have "\<not> (D = C)"
	proof (rule ccontr)
		assume "\<not> (D \<noteq> C)"
		hence "D = C" by blast
		have "bet C G D" using `bet C G D` .
		have "bet C G C" using `bet C G D` `D = C` by blast
		have "\<not> (bet C G C)" using betweennessidentityE[OF `axioms`] .
		show "False" using `\<not> (bet C G C)` `bet C G C` by blast
	qed
	hence "D \<noteq> C" by blast
	have "P \<noteq> E" using betweennotequal[OF `axioms` `bet P E F`] by blast
	have "E \<noteq> P" using inequalitysymmetric[OF `axioms` `P \<noteq> E`] .
	obtain Q where "bet D C Q \<and> seg_eq C Q E P" using extensionE[OF `axioms` `D \<noteq> C` `E \<noteq> P`]  by  blast
	have "bet D C Q" using `bet D C Q \<and> seg_eq C Q E P` by blast
	have "seg_eq C Q E P" using `bet D C Q \<and> seg_eq C Q E P` by blast
	have "bet Q C D" using betweennesssymmetryE[OF `axioms` `bet D C Q`] .
	have "seg_eq Q C C Q" using equalityreverseE[OF `axioms`] .
	have "seg_eq Q C E P" using congruencetransitive[OF `axioms` `seg_eq Q C C Q` `seg_eq C Q E P`] .
	have "seg_eq E P P E" using equalityreverseE[OF `axioms`] .
	have "seg_eq Q C P E" using congruencetransitive[OF `axioms` `seg_eq Q C E P` `seg_eq E P P E`] .
	have "seg_eq Q D P F" using sumofparts[OF `axioms` `seg_eq Q C P E` `seg_eq C D E F` `bet Q C D` `bet P E F`] .
	have "seg_eq C G A B" using `seg_eq C G A B` .
	have "seg_eq E H A B" using `bet P E H \<and> seg_eq E H A B` by blast
	have "seg_eq A B E H" using congruencesymmetric[OF `axioms` `seg_eq E H A B`] .
	have "seg_eq C G E H" using congruencetransitive[OF `axioms` `seg_eq C G A B` `seg_eq A B E H`] .
	have "seg_eq Q D P F" using `seg_eq Q D P F` .
	have "seg_eq C D E F" using `seg_eq C D E F` .
	have "seg_eq Q C P E" using `seg_eq Q C P E` .
	have "seg_eq C G E H" using `seg_eq C G E H` .
	have "bet Q C G" using innertransitivityE[OF `axioms` `bet Q C D` `bet C G D`] .
	have "bet P E H" using `bet P E H \<and> seg_eq E H A B` by blast
	have "seg_eq D G F H" using n5_lineE[OF `axioms` `seg_eq C G E H` `seg_eq Q D P F` `seg_eq C D E F` `bet Q C G` `bet P E H` `seg_eq Q C P E`] .
	have "seg_eq G D H F" using doublereverse[OF `axioms` `seg_eq D G F H`] by blast
	have "seg_eq C G E H" using `seg_eq C G E H` .
	have "seg_eq C D E F" using `seg_eq C D E F` .
	have "bet E H F" using betweennesspreserved[OF `axioms` `seg_eq C G E H` `seg_eq C D E F` `seg_eq G D H F` `bet C G D`] .
	have "seg_lt A B E F" using lessthan_b[OF `axioms` `bet E H F` `seg_eq E H A B`] .
	thus ?thesis by blast
qed

end