theory crossbar
	imports n3_6b n3_7b Geometry betweennotequal collinear4 collinearorder congruencesymmetric congruencetransitive equalitysymmetric extensionunique inequalitysymmetric lessthancongruence raystrict
begin

theorem crossbar:
	assumes "axioms"
		"triangle A B C"
		"bet A E C"
		"ray_on B A U"
		"ray_on B C V"
	shows "\<exists> H. ray_on B E H \<and> bet U H V"
proof -
	have "\<not> col A B C" using triangle_f[OF `axioms` `triangle A B C`] .
	have "\<not> (B = E)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> E)"
		hence "B = E" by blast
		have "\<not> (bet A B C)"
		proof (rule ccontr)
			assume "\<not> (\<not> (bet A B C))"
hence "bet A B C" by blast
			have "col A B C" using collinear_b `axioms` `bet A B C` by blast
			show "False" using `col A B C` `\<not> col A B C` by blast
		qed
		hence "\<not> (bet A B C)" by blast
		have "bet A E C" using `bet A E C` .
		have "bet A B C" using `bet A E C` `B = E` by blast
		show "False" using `bet A B C` `\<not> (bet A B C)` by blast
	qed
	hence "B \<noteq> E" by blast
	have "\<not> (B = A)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> A)"
		hence "B = A" by blast
		have "A = B" using equalitysymmetric[OF `axioms` `B = A`] .
		have "col A B C" using collinear_b `axioms` `A = B` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> A" by blast
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> C)"
		hence "B = C" by blast
		have "col A B C" using collinear_b `axioms` `B = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "B \<noteq> U" using raystrict[OF `axioms` `ray_on B A U`] .
	have "B \<noteq> V" using raystrict[OF `axioms` `ray_on B C V`] .
	obtain P where "bet B A P \<and> seg_eq A P B U" using extensionE[OF `axioms` `B \<noteq> A` `B \<noteq> U`]  by  blast
	obtain Q where "bet B C Q \<and> seg_eq C Q B V" using extensionE[OF `axioms` `B \<noteq> C` `B \<noteq> V`]  by  blast
	have "bet B C Q" using `bet B C Q \<and> seg_eq C Q B V` by blast
	have "\<not> (col B Q A)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B Q A))"
hence "col B Q A" by blast
		have "col Q B A" using collinearorder[OF `axioms` `col B Q A`] by blast
		have "col B C Q" using collinear_b `axioms` `bet B C Q \<and> seg_eq C Q B V` by blast
		have "col Q B C" using collinearorder[OF `axioms` `col B C Q`] by blast
		have "B \<noteq> Q" using betweennotequal[OF `axioms` `bet B C Q`] by blast
		have "Q \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> Q`] .
		have "col B A C" using collinear4[OF `axioms` `col Q B A` `col Q B C` `Q \<noteq> B`] .
		have "col A B C" using collinearorder[OF `axioms` `col B A C`] by blast
		have "\<not> col A B C" using `\<not> col A B C` .
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "\<not> col B Q A" by blast
	obtain F where "bet A F Q \<and> bet B E F" using Pasch_outerE[OF `axioms` `bet A E C` `bet B C Q` `\<not> col B Q A`]  by  blast
	have "bet A F Q" using `bet A F Q \<and> bet B E F` by blast
	have "bet B E F" using `bet A F Q \<and> bet B E F` by blast
	have "bet B A P" using `bet B A P \<and> seg_eq A P B U` by blast
	have "bet Q F A" using betweennesssymmetryE[OF `axioms` `bet A F Q`] .
	have "\<not> (col B P Q)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B P Q))"
hence "col B P Q" by blast
		have "col P B Q" using collinearorder[OF `axioms` `col B P Q`] by blast
		have "col B A P" using collinear_b `axioms` `bet B A P \<and> seg_eq A P B U` by blast
		have "col P B A" using collinearorder[OF `axioms` `col B A P`] by blast
		have "B \<noteq> P" using betweennotequal[OF `axioms` `bet B A P`] by blast
		have "P \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> P`] .
		have "col B Q A" using collinear4[OF `axioms` `col P B Q` `col P B A` `P \<noteq> B`] .
		have "\<not> col B Q A" using `\<not> col B Q A` .
		show "False" using `\<not> col B Q A` `col B Q A` by blast
	qed
	hence "\<not> col B P Q" by blast
	obtain W where "bet Q W P \<and> bet B F W" using Pasch_outerE[OF `axioms` `bet Q F A` `bet B A P` `\<not> col B P Q`]  by  blast
	have "bet B F W" using `bet Q W P \<and> bet B F W` by blast
	have "bet B E W" using n3_6b[OF `axioms` `bet B E F` `bet B F W`] .
	have "ray_on B A U" using `ray_on B A U` .
	obtain J where "bet J B U \<and> bet J B A" using ray_f[OF `axioms` `ray_on B A U`]  by  blast
	have "bet J B A" using `bet J B U \<and> bet J B A` by blast
	have "bet J B U" using `bet J B U \<and> bet J B A` by blast
	have "seg_eq A P P A" using equalityreverseE[OF `axioms`] .
	have "seg_eq A P B U" using `bet B A P \<and> seg_eq A P B U` by blast
	have "seg_eq B U A P" using congruencesymmetric[OF `axioms` `seg_eq A P B U`] .
	have "seg_eq B U P A" using congruencetransitive[OF `axioms` `seg_eq B U A P` `seg_eq A P P A`] .
	have "seg_eq P A B U" using congruencesymmetric[OF `axioms` `seg_eq B U P A`] .
	have "bet P A B" using betweennesssymmetryE[OF `axioms` `bet B A P`] .
	have "seg_lt B U P B" using lessthan_b[OF `axioms` `bet P A B` `seg_eq P A B U`] .
	have "seg_eq P B B P" using equalityreverseE[OF `axioms`] .
	have "seg_lt B U B P" using lessthancongruence[OF `axioms` `seg_lt B U P B` `seg_eq P B B P`] .
	obtain S where "bet B S P \<and> seg_eq B S B U" using lessthan_f[OF `axioms` `seg_lt B U B P`]  by  blast
	have "bet B S P" using `bet B S P \<and> seg_eq B S B U` by blast
	have "seg_eq B S B U" using `bet B S P \<and> seg_eq B S B U` by blast
	have "bet J B P" using n3_7b[OF `axioms` `bet J B A` `bet B A P`] .
	have "bet J B S" using innertransitivityE[OF `axioms` `bet J B P` `bet B S P`] .
	have "S = U" using extensionunique[OF `axioms` `bet J B S` `bet J B U` `seg_eq B S B U`] .
	have "bet B U P" using `bet B S P` `S = U` by blast
	obtain K where "bet K B V \<and> bet K B C" using ray_f[OF `axioms` `ray_on B C V`]  by  blast
	have "bet K B C" using `bet K B V \<and> bet K B C` by blast
	have "bet K B V" using `bet K B V \<and> bet K B C` by blast
	have "seg_eq C Q B V" using `bet B C Q \<and> seg_eq C Q B V` by blast
	have "seg_eq B V C Q" using congruencesymmetric[OF `axioms` `seg_eq C Q B V`] .
	have "seg_eq C Q Q C" using equalityreverseE[OF `axioms`] .
	have "seg_eq B V Q C" using congruencetransitive[OF `axioms` `seg_eq B V C Q` `seg_eq C Q Q C`] .
	have "seg_eq Q C B V" using congruencesymmetric[OF `axioms` `seg_eq B V Q C`] .
	have "bet Q C B" using betweennesssymmetryE[OF `axioms` `bet B C Q`] .
	have "seg_lt B V Q B" using lessthan_b[OF `axioms` `bet Q C B` `seg_eq Q C B V`] .
	have "seg_eq Q B B Q" using equalityreverseE[OF `axioms`] .
	have "seg_lt B V B Q" using lessthancongruence[OF `axioms` `seg_lt B V Q B` `seg_eq Q B B Q`] .
	obtain R where "bet B R Q \<and> seg_eq B R B V" using lessthan_f[OF `axioms` `seg_lt B V B Q`]  by  blast
	have "bet B R Q" using `bet B R Q \<and> seg_eq B R B V` by blast
	have "seg_eq B R B V" using `bet B R Q \<and> seg_eq B R B V` by blast
	have "bet K B Q" using n3_7b[OF `axioms` `bet K B C` `bet B C Q`] .
	have "bet K B R" using innertransitivityE[OF `axioms` `bet K B Q` `bet B R Q`] .
	have "R = V" using extensionunique[OF `axioms` `bet K B R` `bet K B V` `seg_eq B R B V`] .
	have "bet B V Q" using `bet B R Q` `R = V` by blast
	have "bet B V Q" using `bet B V Q` .
	have "bet Q W P" using `bet Q W P \<and> bet B F W` by blast
	have "\<not> (col Q P B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col Q P B))"
hence "col Q P B" by blast
		have "col B P Q" using collinearorder[OF `axioms` `col Q P B`] by blast
		have "\<not> col B P Q" using `\<not> col B P Q` .
		show "False" using `\<not> col B P Q` `col B P Q` by blast
	qed
	hence "\<not> col Q P B" by blast
	obtain M where "bet Q M U \<and> bet B M W" using Pasch_innerE[OF `axioms` `bet Q W P` `bet B U P` `\<not> col Q P B`]  by  blast
	have "bet Q M U" using `bet Q M U \<and> bet B M W` by blast
	have "bet U M Q" using betweennesssymmetryE[OF `axioms` `bet Q M U`] .
	have "\<not> (col U Q B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col U Q B))"
hence "col U Q B" by blast
		have "col B U P" using collinear_b `axioms` `bet B U P` by blast
		have "col B U Q" using collinearorder[OF `axioms` `col U Q B`] by blast
		have "B \<noteq> U" using betweennotequal[OF `axioms` `bet B U P`] by blast
		have "col U B P" using collinearorder[OF `axioms` `col B U P`] by blast
		have "col U B Q" using collinearorder[OF `axioms` `col B U Q`] by blast
		have "U \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> U`] .
		have "col B P Q" using collinear4[OF `axioms` `col U B P` `col U B Q` `U \<noteq> B`] .
		have "col Q P B" using collinearorder[OF `axioms` `col B P Q`] by blast
		have "\<not> col Q P B" using `\<not> col Q P B` .
		show "False" using `\<not> col Q P B` `col Q P B` by blast
	qed
	hence "\<not> col U Q B" by blast
	obtain H where "bet U H V \<and> bet B H M" using Pasch_innerE[OF `axioms` `bet U M Q` `bet B V Q` `\<not> col U Q B`]  by  blast
	have "bet U H V" using `bet U H V \<and> bet B H M` by blast
	have "B \<noteq> E" using `B \<noteq> E` .
	have "\<not> (E = B)"
	proof (rule ccontr)
		assume "\<not> (E \<noteq> B)"
		hence "E = B" by blast
		have "B = E" using equalitysymmetric[OF `axioms` `E = B`] .
		show "False" using `B = E` `B \<noteq> E` by blast
	qed
	hence "E \<noteq> B" by blast
	obtain N where "bet E B N \<and> seg_eq B N B E" using extensionE[OF `axioms` `E \<noteq> B` `B \<noteq> E`]  by  blast
	have "bet E B N" using `bet E B N \<and> seg_eq B N B E` by blast
	have "bet N B E" using betweennesssymmetryE[OF `axioms` `bet E B N`] .
	have "bet B M W" using `bet Q M U \<and> bet B M W` by blast
	have "bet B H M" using `bet U H V \<and> bet B H M` by blast
	have "bet B H W" using n3_6b[OF `axioms` `bet B H M` `bet B M W`] .
	have "bet N B E" using `bet N B E` .
	have "bet B E W" using `bet B E W` .
	have "bet N B W" using n3_7b[OF `axioms` `bet N B E` `bet B E W`] .
	have "bet N B H" using innertransitivityE[OF `axioms` `bet N B W` `bet B H W`] .
	have "ray_on B E H" using ray_b[OF `axioms` `bet N B H` `bet N B E`] .
	have "ray_on B E H \<and> bet U H V" using `ray_on B E H` `bet U H V \<and> bet B H M` by blast
	thus ?thesis by blast
qed

end