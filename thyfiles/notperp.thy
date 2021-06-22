theory notperp
	imports Axioms Definitions Theorems
begin

theorem notperp:
	assumes: `axioms`
		"bet A C B"
		"\<not> col A B P"
	shows: "\<exists> M. \<not> col A B M \<and> same_side M P A B \<and> \<not> (ang_right A C M)"
proof -
	have "C \<noteq> B" using betweennotequal[OF `axioms` `bet A C B`] by blast
	have "B \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> B`] .
	have "\<not> (C = P)"
	proof (rule ccontr)
		assume "C = P"
		have "\<not> col A B C" using `\<not> col A B P` `C = P` by blast
		have "col A C B" using collinear_b `axioms` `bet A C B` by blast
		have "col A B C" using collinearorder[OF `axioms` `col A C B`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "C \<noteq> P" by blast
	obtain Q where "bet B C Q \<and> seg_eq C Q C P" using extensionE[OF `axioms` `B \<noteq> C` `C \<noteq> P`] by blast
	have "bet B C Q" using `bet B C Q \<and> seg_eq C Q C P` by blast
	have "seg_eq C Q C P" using `bet B C Q \<and> seg_eq C Q C P` by blast
	have "\<not> (P = Q)"
	proof (rule ccontr)
		assume "P = Q"
		have "col B C Q" using collinear_b `axioms` `bet B C Q \<and> seg_eq C Q C P` by blast
		have "col B C P" using `col B C Q` `P = Q` by blast
		have "col A C B" using collinear_b `axioms` `bet A C B` by blast
		have "col C B A" using collinearorder[OF `axioms` `col A C B`] by blast
		have "col C B P" using collinearorder[OF `axioms` `col B C P`] by blast
		have "col B A P" using collinear4[OF `axioms` `col C B A` `col C B P` `C \<noteq> B`] .
		have "col A B P" using collinearorder[OF `axioms` `col B A P`] by blast
		show "False" using `col A B P` `\<not> col A B P` by blast
	qed
	hence "P \<noteq> Q" by blast
	obtain M where "bet P M Q \<and> seg_eq M P M Q" using Prop10[OF `axioms` `P \<noteq> Q`] by blast
	have "bet P M Q" using `bet P M Q \<and> seg_eq M P M Q` by blast
	have "seg_eq M P M Q" using `bet P M Q \<and> seg_eq M P M Q` by blast
	have "col A C B" using collinear_b `axioms` `bet A C B` by blast
	have "col C B A" using collinearorder[OF `axioms` `col A C B`] by blast
	have "C \<noteq> B" using betweennotequal[OF `axioms` `bet A C B`] by blast
	have "col C B Q" using collinear_b `axioms` `bet B C Q \<and> seg_eq C Q C P` by blast
	have "col B A Q" using collinear4[OF `axioms` `col C B A` `col C B Q` `C \<noteq> B`] .
	have "col A B Q" using collinearorder[OF `axioms` `col B A Q`] by blast
	have "A \<noteq> B" using betweennotequal[OF `axioms` `bet A C B`] by blast
	have "\<not> col A B P" using `\<not> col A B P` .
	have "same_side P P A B" using samesidereflexive[OF `axioms` `\<not> col A B P`] .
	have "Q \<noteq> P" using inequalitysymmetric[OF `axioms` `P \<noteq> Q`] .
	have "bet Q M P" using betweennesssymmetryE[OF `axioms` `bet P M Q`] .
	have "ray_on Q P M" using ray4 `axioms` `bet Q M P` `Q \<noteq> P` by blast
	have "col A Q B" using collinearorder[OF `axioms` `col A B Q`] by blast
	have "same_side P M A B" using sameside2[OF `axioms` `same_side P P A B` `col A Q B` `ray_on Q P M`] .
	have "same_side M P A B" using samesidesymmetric[OF `axioms` `same_side P M A B`] by blast
	have "\<not> (col A B M)"
	proof (rule ccontr)
		assume "col A B M"
		have "col A B Q" using `col A B Q` .
		have "col B M Q" using collinear4[OF `axioms` `col A B M` `col A B Q` `A \<noteq> B`] .
		have "col P M Q" using collinear_b `axioms` `bet P M Q \<and> seg_eq M P M Q` by blast
		have "col M Q P" using collinearorder[OF `axioms` `col P M Q`] by blast
		have "col M Q B" using collinearorder[OF `axioms` `col B M Q`] by blast
		have "M \<noteq> Q" using betweennotequal[OF `axioms` `bet P M Q`] by blast
		have "col Q P B" using collinear4[OF `axioms` `col M Q P` `col M Q B` `M \<noteq> Q`] .
		have "col Q B P" using collinearorder[OF `axioms` `col Q P B`] by blast
		have "col Q B A" using collinearorder[OF `axioms` `col A B Q`] by blast
		have "B \<noteq> Q" using betweennotequal[OF `axioms` `bet B C Q`] by blast
		have "Q \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> Q`] .
		have "col B P A" using collinear4[OF `axioms` `col Q B P` `col Q B A` `Q \<noteq> B`] .
		have "col A B P" using collinearorder[OF `axioms` `col B P A`] by blast
		show "False" using `col A B P` `\<not> col A B P` by blast
	qed
	hence "\<not> col A B M" by blast
	obtain R where "perp_at M R A B R" using Prop12[OF `axioms` `A \<noteq> B` `\<not> col A B M`] by blast
	obtain E where "col M R R \<and> col A B R \<and> col A B E \<and> ang_right E R M" using perpat_f[OF `axioms` `perp_at M R A B R`] by blast
	have "col A B R" using `col M R R \<and> col A B R \<and> col A B E \<and> ang_right E R M` by blast
	have "ang_right E R M" using `col M R R \<and> col A B R \<and> col A B E \<and> ang_right E R M` by blast
	have "ang_right M R E" using n8_2[OF `axioms` `ang_right E R M`] .
	have "col A B C" using collinearorder[OF `axioms` `col A C B`] by blast
	have "\<not> (ang_right A C M)"
	proof (rule ccontr)
		assume "ang_right A C M"
		have "\<not> (R \<noteq> C)"
		proof (rule ccontr)
			assume "R \<noteq> C"
			have "col B A C" using collinearorder[OF `axioms` `col A B C`] by blast
			have "col A B R" using `col A B R` .
			have "col B A R" using collinearorder[OF `axioms` `col A B R`] by blast
			have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
			have "col A C R" using collinear4[OF `axioms` `col B A C` `col B A R` `B \<noteq> A`] .
			have "ang_right R C M" using collinearright[OF `axioms` `ang_right A C M` `col A C R` `R \<noteq> C`] .
			have "\<not> (ang_right M R C)" using n8_7[OF `axioms` `ang_right R C M`] .
			have "ang_right M R E" using `ang_right M R E` .
			have "ang_right E R M" using n8_2[OF `axioms` `ang_right M R E`] .
			have "col A B E" using `col M R R \<and> col A B R \<and> col A B E \<and> ang_right E R M` by blast
			have "col A B R" using `col A B R` .
			have "col B C R" using collinear4[OF `axioms` `col A B C` `col A B R` `A \<noteq> B`] .
			have "col B C E" using collinear4[OF `axioms` `col A B C` `col A B E` `A \<noteq> B`] .
			have "C \<noteq> B" using betweennotequal[OF `axioms` `bet A C B`] by blast
			have "B \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> B`] .
			have "col C R E" using collinear4[OF `axioms` `col B C R` `col B C E` `B \<noteq> C`] .
			have "col E R C" using collinearorder[OF `axioms` `col C R E`] by blast
			have "C \<noteq> R" using inequalitysymmetric[OF `axioms` `R \<noteq> C`] .
			have "ang_right C R M" using collinearright[OF `axioms` `ang_right E R M` `col E R C` `C \<noteq> R`] .
			have "ang_right M R C" using n8_2[OF `axioms` `ang_right C R M`] .
			show "False" using `ang_right M R C` `\<not> (ang_right M R C)` by blast
		qed
		hence "R = C" by blast
		have "\<not> (M = C)"
		proof (rule ccontr)
			assume "M = C"
			have "col A B C" using `col A B C` .
			have "col A B M" using `col A B C` `M = C` by blast
			show "False" using `col A B M` `\<not> col A B M` by blast
		qed
		hence "M \<noteq> C" by blast
		have "seg_eq Q C P C" using congruenceflip[OF `axioms` `seg_eq C Q C P`] by blast
		have "bet Q M P" using betweennesssymmetryE[OF `axioms` `bet P M Q`] .
		have "seg_eq Q M P M" using doublereverse[OF `axioms` `seg_eq M P M Q`] by blast
		have "ang_right Q M C" using rightangle_b[OF `axioms` `bet Q M P` `seg_eq Q M P M` `seg_eq Q C P C` `M \<noteq> C`] .
		have "C \<noteq> Q" using betweennotequal[OF `axioms` `bet B C Q`] by blast
		have "Q \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> Q`] .
		have "ang_right E R M" using n8_2[OF `axioms` `ang_right M R E`] .
		have "Q \<noteq> R" using `Q \<noteq> C` `R = C` by blast
		have "col A B E" using `col M R R \<and> col A B R \<and> col A B E \<and> ang_right E R M` by blast
		have "col A B Q" using `col A B Q` .
		have "col A B R" using `col A B R` .
		have "col B E R" using collinear4[OF `axioms` `col A B E` `col A B R` `A \<noteq> B`] .
		have "col B E Q" using collinear4[OF `axioms` `col A B E` `col A B Q` `A \<noteq> B`] .
		have "\<not> (B \<noteq> E)"
		proof (rule ccontr)
			assume "B \<noteq> E"
			have "col E R Q" using collinear4[OF `axioms` `col B E R` `col B E Q` `B \<noteq> E`] .
			have "ang_right Q R M" using collinearright[OF `axioms` `ang_right E R M` `col E R Q` `Q \<noteq> R`] .
			have "ang_right Q C M" using `ang_right Q R M` `R = C` by blast
			have "ang_right M C Q" using n8_2[OF `axioms` `ang_right Q C M`] .
			have "\<not> (ang_right Q M C)" using n8_7[OF `axioms` `ang_right M C Q`] .
			show "False" using `\<not> (ang_right Q M C)` `ang_right Q M C` by blast
		qed
		hence "B = E" by blast
		have "col A B R" using `col A B R` .
		have "col A E R" using `col A B C` `B = E` `R = C` by blast
		have "col A B Q" using collinearorder[OF `axioms` `col A Q B`] by blast
		have "col A E Q" using `col A B Q` `B = E` by blast
		have "A \<noteq> E" using `A \<noteq> B` `B = E` by blast
		have "col E R Q" using collinear4[OF `axioms` `col A E R` `col A E Q` `A \<noteq> E`] .
		have "ang_right Q R M" using collinearright[OF `axioms` `ang_right E R M` `col E R Q` `Q \<noteq> R`] .
		have "ang_right Q C M" using `ang_right Q R M` `R = C` by blast
		have "ang_right M C Q" using n8_2[OF `axioms` `ang_right Q C M`] .
		have "\<not> (ang_right Q M C)" using n8_7[OF `axioms` `ang_right M C Q`] .
		show "False" using `\<not> (ang_right Q M C)` `ang_right Q M C` by blast
	qed
	hence "\<not> (ang_right A C M)" by blast
	have "\<not> col A B M \<and> same_side M P A B \<and> \<not> (ang_right A C M)" using `\<not> col A B M` `same_side M P A B` `\<not> (ang_right A C M)` by blast
	thus ?thesis by blast
qed

end