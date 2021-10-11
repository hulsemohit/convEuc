theory supplementinequality
	imports n3_7b ABCequalsCBA Geometry angleorderrespectscongruence angleorderrespectscongruence2 betweennotequal collinear4 collinearorder equalanglesNC equalanglesflip equalangleshelper equalanglesreflexive equalanglessymmetric equalanglestransitive inequalitysymmetric ray1 ray3 ray4 ray5 rayimpliescollinear raystrict supplements
begin

theorem(in euclidean_geometry) supplementinequality:
	assumes 
		"supplement A B C D F"
		"supplement a b c d f"
		"ang_lt a b c A B C"
	shows "ang_lt D B F d b f"
proof -
	obtain P Q R where "bet P R Q \<and> ray_on B A P \<and> ray_on B C Q \<and> ang_eq a b c A B R" using anglelessthan_f[OF `ang_lt a b c A B C`]  by  blast
	have "bet P R Q" using `bet P R Q \<and> ray_on B A P \<and> ray_on B C Q \<and> ang_eq a b c A B R` by blast
	have "ray_on B C Q" using `bet P R Q \<and> ray_on B A P \<and> ray_on B C Q \<and> ang_eq a b c A B R` by blast
	have "ang_eq a b c A B R" using `bet P R Q \<and> ray_on B A P \<and> ray_on B C Q \<and> ang_eq a b c A B R` by blast
	have "\<not> col A B R" using equalanglesNC[OF `ang_eq a b c A B R`] .
	have "ray_on B C D \<and> bet A B F" using supplement_f[OF `supplement A B C D F`] .
	have "bet Q R P" using betweennesssymmetryE[OF `bet P R Q`] .
	have "bet A B F" using `ray_on B C D \<and> bet A B F` by blast
	have "bet F B A" using betweennesssymmetryE[OF `bet A B F`] .
	have "ray_on B A P" using `bet P R Q \<and> ray_on B A P \<and> ray_on B C Q \<and> ang_eq a b c A B R` by blast
	have "bet B P A \<or> A = P \<or> bet B A P" using ray1[OF `ray_on B A P`] .
	consider "bet B P A"|"A = P"|"bet B A P" using `bet B P A \<or> A = P \<or> bet B A P`  by blast
	hence "bet F B P"
	proof (cases)
		assume "bet B P A"
		have "bet F B P" using innertransitivityE[OF `bet F B A` `bet B P A`] .
		thus ?thesis by blast
	next
		assume "A = P"
		have "bet F B P" using `bet F B A` `A = P` by blast
		thus ?thesis by blast
	next
		assume "bet B A P"
		have "bet F B P" using n3_7b[OF `bet F B A` `bet B A P`] .
		thus ?thesis by blast
	qed
	have "\<not> (col F P Q)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col F P Q))"
hence "col F P Q" by blast
		have "col B A P" using rayimpliescollinear[OF `ray_on B A P`] .
		have "col A B F" using collinear_b `ray_on B C D \<and> bet A B F` by blast
		have "A \<noteq> B" using betweennotequal[OF `bet A B F`] by blast
		have "col A B P" using collinearorder[OF `col B A P`] by blast
		have "col B F P" using collinear4[OF `col A B F` `col A B P` `A \<noteq> B`] .
		have "col F P B" using collinearorder[OF `col B F P`] by blast
		have "F \<noteq> P" using betweennotequal[OF `bet F B P`] by blast
		have "col P Q B" using collinear4[OF `col F P Q` `col F P B` `F \<noteq> P`] .
		have "col P B Q" using collinearorder[OF `col P Q B`] by blast
		have "col P B A" using collinearorder[OF `col A B P`] by blast
		have "B \<noteq> P" using betweennotequal[OF `bet F B P`] by blast
		have "P \<noteq> B" using inequalitysymmetric[OF `B \<noteq> P`] .
		have "col B Q A" using collinear4[OF `col P B Q` `col P B A` `P \<noteq> B`] .
		have "col P R Q" using collinear_b `bet P R Q \<and> ray_on B A P \<and> ray_on B C Q \<and> ang_eq a b c A B R` by blast
		have "col P Q R" using collinearorder[OF `col P R Q`] by blast
		have "col P Q B" using collinearorder[OF `col P B Q`] by blast
		have "P \<noteq> Q" using betweennotequal[OF `bet P R Q`] by blast
		have "col Q R B" using collinear4[OF `col P Q R` `col P Q B` `P \<noteq> Q`] .
		have "col Q B R" using collinearorder[OF `col Q R B`] by blast
		have "col Q B A" using collinearorder[OF `col B Q A`] by blast
		have "B \<noteq> Q" using raystrict[OF `ray_on B C Q`] .
		have "Q \<noteq> B" using inequalitysymmetric[OF `B \<noteq> Q`] .
		have "col B R A" using collinear4[OF `col Q B R` `col Q B A` `Q \<noteq> B`] .
		have "col A B R" using collinearorder[OF `col B R A`] by blast
		have "\<not> col A B R" using `\<not> col A B R` .
		show "False" using `\<not> col A B R` `col A B R` by blast
	qed
	hence "\<not> col F P Q" by blast
	obtain M where "bet F M R \<and> bet Q M B" using Pasch_innerE[OF `bet F B P` `bet Q R P` `\<not> col F P Q`]  by  blast
	have "bet F M R" using `bet F M R \<and> bet Q M B` by blast
	have "bet Q M B" using `bet F M R \<and> bet Q M B` by blast
	have "R = R" using equalityreflexiveE.
	have "\<not> (B = R)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> R)"
		hence "B = R" by blast
		have "col A B R" using collinear_b `B = R` by blast
		show "False" using `col A B R` `\<not> col A B R` by blast
	qed
	hence "B \<noteq> R" by blast
	have "ray_on B R R" using ray4 `R = R` `B \<noteq> R` by blast
	have "supplement A B R R F" using supplement_b[OF `ray_on B R R` `bet A B F`] .
	have "ang_eq A B R a b c" using equalanglessymmetric[OF `ang_eq a b c A B R`] .
	have "ang_eq R B F d b f" using supplements[OF `ang_eq A B R a b c` `supplement A B R R F` `supplement a b c d f`] .
	have "B \<noteq> F" using betweennotequal[OF `bet A B F`] by blast
	have "F = F" using equalityreflexiveE.
	have "ray_on B F F" using ray4 `F = F` `B \<noteq> F` by blast
	have "ang_eq d b f R B F" using equalanglessymmetric[OF `ang_eq R B F d b f`] .
	have "\<not> col R B F" using equalanglesNC[OF `ang_eq d b f R B F`] .
	have "\<not> (col F B Q)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col F B Q))"
hence "col F B Q" by blast
		have "col Q B F" using collinearorder[OF `col F B Q`] by blast
		have "col Q M B" using collinear_b `bet F M R \<and> bet Q M B` by blast
		have "col Q B M" using collinearorder[OF `col Q M B`] by blast
		have "Q \<noteq> B" using betweennotequal[OF `bet Q M B`] by blast
		have "col B F M" using collinear4[OF `col Q B F` `col Q B M` `Q \<noteq> B`] .
		have "col F M R" using collinear_b `bet F M R \<and> bet Q M B` by blast
		have "col M F B" using collinearorder[OF `col B F M`] by blast
		have "col M F R" using collinearorder[OF `col F M R`] by blast
		have "F \<noteq> M" using betweennotequal[OF `bet F M R`] by blast
		have "M \<noteq> F" using inequalitysymmetric[OF `F \<noteq> M`] .
		have "col F B R" using collinear4[OF `col M F B` `col M F R` `M \<noteq> F`] .
		have "col R B F" using collinearorder[OF `col F B R`] by blast
		show "False" using `col R B F` `\<not> col R B F` by blast
	qed
	hence "\<not> col F B Q" by blast
	have "ray_on B F F" using `ray_on B F F` .
	have "ang_eq F B Q F B Q" using equalanglesreflexive[OF `\<not> col F B Q`] .
	have "bet B M Q" using betweennesssymmetryE[OF `bet Q M B`] .
	have "B \<noteq> M" using betweennotequal[OF `bet B M Q`] by blast
	have "ray_on B M Q" using ray4 `bet B M Q` `B \<noteq> M` by blast
	have "ray_on B Q M" using ray5[OF `ray_on B M Q`] .
	have "ang_eq F B Q F B M" using equalangleshelper[OF `ang_eq F B Q F B Q` `ray_on B F F` `ray_on B Q M`] .
	have "bet R M F" using betweennesssymmetryE[OF `bet F M R`] .
	have "ray_on B R R" using `ray_on B R R` .
	have "ray_on B F F" using `ray_on B F F` .
	have "ang_lt F B Q F B R" using anglelessthan_b[OF `bet F M R` `ray_on B F F` `ray_on B R R` `ang_eq F B Q F B M`] .
	have "ang_eq f b d F B R" using equalanglesflip[OF `ang_eq d b f R B F`] .
	have "ang_eq F B R f b d" using equalanglessymmetric[OF `ang_eq f b d F B R`] .
	have "ang_lt F B Q f b d" using angleorderrespectscongruence[OF `ang_lt F B Q F B R` `ang_eq f b d F B R`] .
	have "ray_on B C Q" using `ray_on B C Q` .
	have "ray_on B C D" using `ray_on B C D \<and> bet A B F` by blast
	have "ray_on B Q D" using ray3[OF `ray_on B C Q` `ray_on B C D`] .
	have "ang_eq F B Q F B D" using equalangleshelper[OF `ang_eq F B Q F B Q` `ray_on B F F` `ray_on B Q D`] .
	have "\<not> (col F B D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col F B D))"
hence "col F B D" by blast
		have "col B Q D" using rayimpliescollinear[OF `ray_on B Q D`] .
		have "col D B Q" using collinearorder[OF `col B Q D`] by blast
		have "col D B F" using collinearorder[OF `col F B D`] by blast
		have "B \<noteq> D" using raystrict[OF `ray_on B C D`] .
		have "D \<noteq> B" using inequalitysymmetric[OF `B \<noteq> D`] .
		have "col B Q F" using collinear4[OF `col D B Q` `col D B F` `D \<noteq> B`] .
		have "col F B Q" using collinearorder[OF `col B Q F`] by blast
		have "\<not> col F B Q" using `\<not> col F B Q` .
		show "False" using `\<not> col F B Q` `col F B Q` by blast
	qed
	hence "\<not> col F B D" by blast
	have "ang_eq F B D D B F" using ABCequalsCBA[OF `\<not> col F B D`] .
	have "ang_eq F B Q D B F" using equalanglestransitive[OF `ang_eq F B Q F B D` `ang_eq F B D D B F`] .
	have "ang_eq D B F F B Q" using equalanglessymmetric[OF `ang_eq F B Q D B F`] .
	have "ang_lt D B F f b d" using angleorderrespectscongruence2[OF `ang_lt F B Q f b d` `ang_eq D B F F B Q`] .
	have "\<not> col f b d" using equalanglesNC[OF `ang_eq F B R f b d`] .
	have "\<not> (col d b f)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col d b f))"
hence "col d b f" by blast
		have "col f b d" using collinearorder[OF `col d b f`] by blast
		show "False" using `col f b d` `\<not> col f b d` by blast
	qed
	hence "\<not> col d b f" by blast
	have "ang_eq d b f f b d" using ABCequalsCBA[OF `\<not> col d b f`] .
	have "ang_lt D B F d b f" using angleorderrespectscongruence[OF `ang_lt D B F f b d` `ang_eq d b f f b d`] .
	thus ?thesis by blast
qed

end