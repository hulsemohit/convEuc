theory Prop40
	imports Geometry NCdistinct NChelper NCorder Prop31short Prop38 Prop39 betweennotequal collinear4 collinearorder collinearparallel congruencesymmetric inequalitysymmetric
begin

theorem(in euclidean_geometry) Prop40:
	assumes 
		"seg_eq B C H E"
		"tri_eq_area A B C D H E"
		"triangle A B C"
		"triangle D H E"
		"col B C H"
		"col B C E"
		"same_side A D B C"
		"A \<noteq> D"
	shows "parallel A D B C"
proof -
	have "\<not> col D H E" using triangle_f[OF `triangle D H E`] .
	have "H \<noteq> E" using NCdistinct[OF `\<not> col D H E`] by blast
	have "E \<noteq> H" using inequalitysymmetric[OF `H \<noteq> E`] .
	obtain R where "bet E H R \<and> seg_eq H R E H" using extensionE[OF `E \<noteq> H` `E \<noteq> H`]  by  blast
	have "bet E H R" using `bet E H R \<and> seg_eq H R E H` by blast
	have "bet R H E" using betweennesssymmetryE[OF `bet E H R`] .
	have "\<not> col H E D" using NCorder[OF `\<not> col D H E`] by blast
	have "col R H E" using collinear_b `bet R H E` by blast
	have "col H E R" using collinearorder[OF `col R H E`] by blast
	have "E = E" using equalityreflexiveE.
	have "col H E E" using collinear_b `E = E` by blast
	have "R \<noteq> E" using betweennotequal[OF `bet R H E`] by blast
	have "\<not> col R E D" using NChelper[OF `\<not> col H E D` `col H E R` `col H E E` `R \<noteq> E`] .
	obtain M P Q where "bet P D Q \<and> ang_eq P D H D H E \<and> parallel P Q R E \<and> bet P M E \<and> bet D M H" using Prop31short[OF `bet R H E` `\<not> col R E D`]  by  blast
	have "bet P D Q" using `bet P D Q \<and> ang_eq P D H D H E \<and> parallel P Q R E \<and> bet P M E \<and> bet D M H` by blast
	have "parallel P Q R E" using `bet P D Q \<and> ang_eq P D H D H E \<and> parallel P Q R E \<and> bet P M E \<and> bet D M H` by blast
	have "col R E H" using collinearorder[OF `col H E R`] by blast
	have "parallel P Q H E" using collinearparallel[OF `parallel P Q R E` `col R E H` `H \<noteq> E`] .
	have "col P D Q" using collinear_b `bet P D Q \<and> ang_eq P D H D H E \<and> parallel P Q R E \<and> bet P M E \<and> bet D M H` by blast
	have "col P Q D" using collinearorder[OF `col P D Q`] by blast
	have "seg_eq H E B C" using congruencesymmetric[OF `seg_eq B C H E`] .
	have "col C B H" using collinearorder[OF `col B C H`] by blast
	have "col C B E" using collinearorder[OF `col B C E`] by blast
	have "\<not> col A B C" using triangle_f[OF `triangle A B C`] .
	have "B \<noteq> C" using NCdistinct[OF `\<not> col A B C`] by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `B \<noteq> C`] .
	have "col B H E" using collinear4[OF `col C B H` `col C B E` `C \<noteq> B`] .
	have "col H E B" using collinearorder[OF `col B H E`] by blast
	have "col B C H" using collinearorder[OF `col C B H`] by blast
	have "col B C E" using collinearorder[OF `col C B E`] by blast
	have "col C H E" using collinear4[OF `col B C H` `col B C E` `B \<noteq> C`] .
	have "col H E C" using collinearorder[OF `col C H E`] by blast
	have "tri_eq_area D H E D B C" using Prop38[OF `parallel P Q H E` `col P Q D` `col P Q D` `seg_eq H E B C` `col H E B` `col H E C`] .
	have "tri_eq_area A B C D B C" using ETtransitiveE[OF `tri_eq_area A B C D H E` `tri_eq_area D H E D B C`] .
	have "\<not> col H E D" using NCorder[OF `\<not> col D H E`] by blast
	have "col H E B" using `col H E B` .
	have "col H E C" using `col H E C` .
	have "B \<noteq> C" using `B \<noteq> C` .
	have "\<not> col B C D" using NChelper[OF `\<not> col H E D` `col H E B` `col H E C` `B \<noteq> C`] .
	have "\<not> col D B C" using NCorder[OF `\<not> col B C D`] by blast
	have "triangle D B C" using triangle_b[OF `\<not> col D B C`] .
	have "parallel A D B C" using Prop39[OF `triangle A B C` `triangle D B C` `same_side A D B C` `tri_eq_area A B C D B C` `A \<noteq> D`] .
	thus ?thesis by blast
qed

end