theory angleordertransitive
	imports n3_6b Geometry angledistinct angleorderrespectscongruence collinear4 collinearorder crossbar equalanglesNC equalangleshelper equalanglessymmetric inequalitysymmetric ray2 ray4 ray5 rayimpliescollinear raystrict
begin

theorem(in euclidean_geometry) angleordertransitive:
	assumes 
		"ang_lt A B C D E F"
		"ang_lt D E F P Q R"
	shows "ang_lt A B C P Q R"
proof -
	obtain U V W where "bet U W V \<and> ray_on Q P U \<and> ray_on Q R V \<and> ang_eq D E F P Q W" using anglelessthan_f[OF `ang_lt D E F P Q R`]  by  blast
	have "ray_on Q P U" using `bet U W V \<and> ray_on Q P U \<and> ray_on Q R V \<and> ang_eq D E F P Q W` by blast
	have "ray_on Q R V" using `bet U W V \<and> ray_on Q P U \<and> ray_on Q R V \<and> ang_eq D E F P Q W` by blast
	have "ang_eq D E F P Q W" using `bet U W V \<and> ray_on Q P U \<and> ray_on Q R V \<and> ang_eq D E F P Q W` by blast
	have "ang_eq P Q W D E F" using equalanglessymmetric[OF `ang_eq D E F P Q W`] .
	have "Q \<noteq> W" using angledistinct[OF `ang_eq D E F P Q W`] by blast
	have "ang_eq D E F P Q W" using `ang_eq D E F P Q W` .
	have "W = W" using equalityreflexiveE.
	have "ray_on Q W W" using ray4 `W = W` `Q \<noteq> W` by blast
	have "ray_on Q W W" using `ray_on Q W W` .
	have "ang_eq D E F U Q W" using equalangleshelper[OF `ang_eq D E F P Q W` `ray_on Q P U` `ray_on Q W W`] .
	have "ang_eq U Q W D E F" using equalanglessymmetric[OF `ang_eq D E F U Q W`] .
	have "ang_lt A B C U Q W" using angleorderrespectscongruence[OF `ang_lt A B C D E F` `ang_eq U Q W D E F`] .
	obtain H S T where "bet S H T \<and> ray_on Q U S \<and> ray_on Q W T \<and> ang_eq A B C U Q H" using anglelessthan_f[OF `ang_lt A B C U Q W`]  by  blast
	have "ray_on Q P U" using `ray_on Q P U` .
	have "ray_on Q U P" using ray5[OF `ray_on Q P U`] .
	have "ray_on Q U S" using `bet S H T \<and> ray_on Q U S \<and> ray_on Q W T \<and> ang_eq A B C U Q H` by blast
	have "ang_eq A B C U Q H" using `bet S H T \<and> ray_on Q U S \<and> ray_on Q W T \<and> ang_eq A B C U Q H` by blast
	have "Q \<noteq> H" using angledistinct[OF `ang_eq A B C U Q H`] by blast
	have "H = H" using equalityreflexiveE.
	have "ray_on Q H H" using ray4 `H = H` `Q \<noteq> H` by blast
	have "ang_eq A B C P Q H" using equalangleshelper[OF `ang_eq A B C U Q H` `ray_on Q U P` `ray_on Q H H`] .
	have "ang_eq D E F U Q W" using `ang_eq D E F U Q W` .
	have "ray_on Q U P" using `ray_on Q U P` .
	have "ray_on Q W T" using `bet S H T \<and> ray_on Q U S \<and> ray_on Q W T \<and> ang_eq A B C U Q H` by blast
	have "ang_eq D E F P Q T" using equalangleshelper[OF `ang_eq D E F U Q W` `ray_on Q U P` `ray_on Q W T`] .
	have "\<not> col P Q T" using equalanglesNC[OF `ang_eq D E F P Q T`] .
	have "bet S H T" using `bet S H T \<and> ray_on Q U S \<and> ray_on Q W T \<and> ang_eq A B C U Q H` by blast
	have "ray_on Q P U" using `ray_on Q P U` .
	have "Q \<noteq> P" using ray2[OF `ray_on Q P U`] .
	have "ray_on Q T W" using ray5[OF `ray_on Q W T`] .
	have "\<not> (col S Q T)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col S Q T))"
hence "col S Q T" by blast
		have "col Q U S" using rayimpliescollinear[OF `ray_on Q U S`] .
		have "col U Q S" using collinearorder[OF `col Q U S`] by blast
		have "ray_on Q P U" using `ray_on Q P U` .
		have "col Q P U" using rayimpliescollinear[OF `ray_on Q P U`] .
		have "col U Q P" using collinearorder[OF `col Q P U`] by blast
		have "Q \<noteq> U" using raystrict[OF `ray_on Q P U`] .
		have "U \<noteq> Q" using inequalitysymmetric[OF `Q \<noteq> U`] .
		have "col Q S P" using collinear4[OF `col U Q S` `col U Q P` `U \<noteq> Q`] .
		have "col S Q P" using collinearorder[OF `col Q S P`] by blast
		have "Q \<noteq> S" using raystrict[OF `ray_on Q U S`] .
		have "S \<noteq> Q" using inequalitysymmetric[OF `Q \<noteq> S`] .
		have "col Q T P" using collinear4[OF `col S Q T` `col S Q P` `S \<noteq> Q`] .
		have "col P Q T" using collinearorder[OF `col Q T P`] by blast
		show "False" using `col P Q T` `\<not> col P Q T` by blast
	qed
	hence "\<not> col S Q T" by blast
	have "triangle S Q T" using triangle_b[OF `\<not> col S Q T`] .
	have "ray_on Q S U" using ray5[OF `ray_on Q U S`] .
	have "ray_on Q T W" using `ray_on Q T W` .
	obtain K where "ray_on Q H K \<and> bet U K W" using crossbar[OF `triangle S Q T` `bet S H T` `ray_on Q S U` `ray_on Q T W`]  by  blast
	have "ray_on Q H K" using `ray_on Q H K \<and> bet U K W` by blast
	have "bet U K W" using `ray_on Q H K \<and> bet U K W` by blast
	have "bet U W V" using `bet U W V \<and> ray_on Q P U \<and> ray_on Q R V \<and> ang_eq D E F P Q W` by blast
	have "bet U K V" using n3_6b[OF `bet U K W` `bet U W V`] .
	have "ang_eq A B C P Q H" using `ang_eq A B C P Q H` .
	have "P = P" using equalityreflexiveE.
	have "ray_on Q P P" using ray4 `P = P` `Q \<noteq> P` by blast
	have "ang_eq A B C P Q K" using equalangleshelper[OF `ang_eq A B C P Q H` `ray_on Q P P` `ray_on Q H K`] .
	have "ang_lt A B C P Q R" using anglelessthan_b[OF `bet U K V` `ray_on Q P U` `ray_on Q R V` `ang_eq A B C P Q K`] .
	thus ?thesis by blast
qed

end