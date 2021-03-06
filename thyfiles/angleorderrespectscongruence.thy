theory angleorderrespectscongruence
	imports ABCequalsCBA Geometry NCdistinct NCorder Prop03 Prop04 angledistinct betweennotequal collinearorder congruenceflip congruencesymmetric equalanglesNC equalangleshelper equalanglessymmetric equalanglestransitive inequalitysymmetric layoff ray4 ray5 raystrict
begin

theorem(in euclidean_geometry) angleorderrespectscongruence:
	assumes 
		"ang_lt A B C D E F"
		"ang_eq P Q R D E F"
	shows "ang_lt A B C P Q R"
proof -
	obtain G H J where "bet G H J \<and> ray_on E D G \<and> ray_on E F J \<and> ang_eq A B C D E H" using anglelessthan_f[OF `ang_lt A B C D E F`]  by  blast
	have "bet G H J" using `bet G H J \<and> ray_on E D G \<and> ray_on E F J \<and> ang_eq A B C D E H` by blast
	have "ray_on E D G" using `bet G H J \<and> ray_on E D G \<and> ray_on E F J \<and> ang_eq A B C D E H` by blast
	have "ray_on E F J" using `bet G H J \<and> ray_on E D G \<and> ray_on E F J \<and> ang_eq A B C D E H` by blast
	have "ang_eq A B C D E H" using `bet G H J \<and> ray_on E D G \<and> ray_on E F J \<and> ang_eq A B C D E H` by blast
	have "P \<noteq> Q \<and> Q \<noteq> R \<and> P \<noteq> R \<and> D \<noteq> E \<and> E \<noteq> F \<and> D \<noteq> F" using angledistinct[OF `ang_eq P Q R D E F`] .
	have "P \<noteq> Q" using `P \<noteq> Q \<and> Q \<noteq> R \<and> P \<noteq> R \<and> D \<noteq> E \<and> E \<noteq> F \<and> D \<noteq> F` by blast
	have "Q \<noteq> R" using `P \<noteq> Q \<and> Q \<noteq> R \<and> P \<noteq> R \<and> D \<noteq> E \<and> E \<noteq> F \<and> D \<noteq> F` by blast
	have "Q \<noteq> P" using inequalitysymmetric[OF `P \<noteq> Q`] .
	have "A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C \<and> D \<noteq> E \<and> E \<noteq> H \<and> D \<noteq> H" using angledistinct[OF `ang_eq A B C D E H`] .
	have "E \<noteq> G" using raystrict[OF `ray_on E D G`] .
	obtain U where "ray_on Q P U \<and> seg_eq Q U E G" using layoff[OF `Q \<noteq> P` `E \<noteq> G`]  by  blast
	have "seg_eq Q U E G" using `ray_on Q P U \<and> seg_eq Q U E G` by blast
	have "E \<noteq> J" using raystrict[OF `ray_on E F J`] .
	obtain V where "ray_on Q R V \<and> seg_eq Q V E J" using layoff[OF `Q \<noteq> R` `E \<noteq> J`]  by  blast
	have "seg_eq Q V E J" using `ray_on Q R V \<and> seg_eq Q V E J` by blast
	have "seg_eq G H G H" using congruencereflexiveE.
	have "seg_lt G H G J" using lessthan_b[OF `bet G H J` `seg_eq G H G H`] .
	have "ray_on Q P U" using `ray_on Q P U \<and> seg_eq Q U E G` by blast
	have "ray_on Q R V" using `ray_on Q R V \<and> seg_eq Q V E J` by blast
	have "ang_eq D E F P Q R" using equalanglessymmetric[OF `ang_eq P Q R D E F`] .
	have "ang_eq D E F U Q V" using equalangleshelper[OF `ang_eq D E F P Q R` `ray_on Q P U` `ray_on Q R V`] .
	have "ray_on E D G" using `ray_on E D G` .
	have "ray_on E F J" using `ray_on E F J` .
	have "ang_eq U Q V D E F" using equalanglessymmetric[OF `ang_eq D E F U Q V`] .
	have "ang_eq U Q V G E J" using equalangleshelper[OF `ang_eq U Q V D E F` `ray_on E D G` `ray_on E F J`] .
	have "ang_eq G E J U Q V" using equalanglessymmetric[OF `ang_eq U Q V G E J`] .
	have "ang_eq G E J U Q V" using `ang_eq G E J U Q V` .
	have "seg_eq E G Q U" using congruencesymmetric[OF `seg_eq Q U E G`] .
	have "seg_eq E J Q V" using congruencesymmetric[OF `seg_eq Q V E J`] .
	have "seg_eq G J U V \<and> ang_eq E G J Q U V \<and> ang_eq E J G Q V U" using Prop04[OF `seg_eq E G Q U` `seg_eq E J Q V` `ang_eq G E J U Q V`] .
	have "seg_eq G J U V" using `seg_eq G J U V \<and> ang_eq E G J Q U V \<and> ang_eq E J G Q V U` by blast
	have "ang_eq E G J Q U V" using `seg_eq G J U V \<and> ang_eq E G J Q U V \<and> ang_eq E J G Q V U` by blast
	have "seg_eq U V G J" using congruencesymmetric[OF `seg_eq G J U V`] .
	have "seg_lt G H G J" using `seg_lt G H G J` .
	have "G \<noteq> J" using betweennotequal[OF `bet G H J`] by blast
	obtain W where "bet U W V \<and> seg_eq U W G H" using Prop03[OF `seg_lt G H G J` `seg_eq U V G J`]  by  blast
	have "bet U W V" using `bet U W V \<and> seg_eq U W G H` by blast
	have "seg_eq U W G H" using `bet U W V \<and> seg_eq U W G H` by blast
	have "ray_on E D G" using `ray_on E D G` .
	have "H = H" using equalityreflexiveE.
	have "E \<noteq> H" using `A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C \<and> D \<noteq> E \<and> E \<noteq> H \<and> D \<noteq> H` by blast
	have "ray_on E H H" using ray4 `H = H` `A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C \<and> D \<noteq> E \<and> E \<noteq> H \<and> D \<noteq> H` by blast
	have "ang_eq A B C G E H" using equalangleshelper[OF `ang_eq A B C D E H` `ray_on E D G` `ray_on E H H`] .
	have "\<not> col G E H" using equalanglesNC[OF `ang_eq A B C G E H`] .
	have "\<not> col G H E" using NCorder[OF `\<not> col G E H`] by blast
	have "U \<noteq> V" using betweennotequal[OF `bet U W V`] by blast
	have "ray_on U V W" using ray4 `bet U W V \<and> seg_eq U W G H` `U \<noteq> V` by blast
	have "Q = Q" using equalityreflexiveE.
	have "E = E" using equalityreflexiveE.
	have "\<not> col U Q V" using equalanglesNC[OF `ang_eq D E F U Q V`] .
	have "U \<noteq> Q" using NCdistinct[OF `\<not> col U Q V`] by blast
	have "ray_on U Q Q" using ray4 `Q = Q` `U \<noteq> Q` by blast
	have "\<not> (G = E)"
	proof (rule ccontr)
		assume "\<not> (G \<noteq> E)"
		hence "G = E" by blast
		have "col G H E" using collinear_b `G = E` by blast
		show "False" using `col G H E` `\<not> col G H E` by blast
	qed
	hence "G \<noteq> E" by blast
	have "ray_on G E E" using ray4 `E = E` `G \<noteq> E` by blast
	have "ang_eq E G J Q U W" using equalangleshelper[OF `ang_eq E G J Q U V` `ray_on U Q Q` `ray_on U V W`] .
	have "ang_eq Q U W E G J" using equalanglessymmetric[OF `ang_eq E G J Q U W`] .
	have "ray_on G J H" using ray4 `bet G H J \<and> ray_on E D G \<and> ray_on E F J \<and> ang_eq A B C D E H` `G \<noteq> J` by blast
	have "ang_eq Q U W E G H" using equalangleshelper[OF `ang_eq Q U W E G J` `ray_on G E E` `ray_on G J H`] .
	have "ang_eq E G H Q U W" using equalanglessymmetric[OF `ang_eq Q U W E G H`] .
	have "\<not> col Q U W" using equalanglesNC[OF `ang_eq E G H Q U W`] .
	have "\<not> col U W Q" using NCorder[OF `\<not> col Q U W`] by blast
	have "\<not> col H G E" using NCorder[OF `\<not> col G E H`] by blast
	have "\<not> (col W U Q)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col W U Q))"
hence "col W U Q" by blast
		have "col U W Q" using collinearorder[OF `col W U Q`] by blast
		show "False" using `col U W Q` `\<not> col U W Q` by blast
	qed
	hence "\<not> col W U Q" by blast
	have "seg_eq G H U W" using congruencesymmetric[OF `seg_eq U W G H`] .
	have "seg_eq G E U Q" using congruenceflip[OF `seg_eq E G Q U`] by blast
	have "ang_eq Q U W E G H" using `ang_eq Q U W E G H` .
	have "ang_eq E G H Q U W" using equalanglessymmetric[OF `ang_eq Q U W E G H`] .
	have "\<not> col Q U W" using `\<not> col Q U W` .
	have "ang_eq Q U W W U Q" using ABCequalsCBA[OF `\<not> col Q U W`] .
	have "ang_eq E G H W U Q" using equalanglestransitive[OF `ang_eq E G H Q U W` `ang_eq Q U W W U Q`] .
	have "ang_eq H G E E G H" using ABCequalsCBA[OF `\<not> col H G E`] .
	have "ang_eq H G E W U Q" using equalanglestransitive[OF `ang_eq H G E E G H` `ang_eq E G H W U Q`] .
	have "seg_eq H E W Q \<and> ang_eq G H E U W Q \<and> ang_eq G E H U Q W" using Prop04[OF `seg_eq G H U W` `seg_eq G E U Q` `ang_eq H G E W U Q`] .
	have "ang_eq G E H U Q W" using `seg_eq H E W Q \<and> ang_eq G H E U W Q \<and> ang_eq G E H U Q W` by blast
	have "ang_eq A B C G E H" using `ang_eq A B C G E H` .
	have "ang_eq A B C U Q W" using equalanglestransitive[OF `ang_eq A B C G E H` `ang_eq G E H U Q W`] .
	have "W = W" using equalityreflexiveE.
	have "\<not> (Q = W)"
	proof (rule ccontr)
		assume "\<not> (Q \<noteq> W)"
		hence "Q = W" by blast
		have "col Q U W" using collinear_b `Q = W` by blast
		have "col W U Q" using collinearorder[OF `col Q U W`] by blast
		show "False" using `col W U Q` `\<not> col W U Q` by blast
	qed
	hence "Q \<noteq> W" by blast
	have "ray_on Q W W" using ray4 `W = W` `Q \<noteq> W` by blast
	have "ray_on Q U P" using ray5[OF `ray_on Q P U`] .
	have "ang_eq A B C P Q W" using equalangleshelper[OF `ang_eq A B C U Q W` `ray_on Q U P` `ray_on Q W W`] .
	have "ray_on Q P U" using `ray_on Q P U` .
	have "ray_on Q R V" using `ray_on Q R V` .
	have "bet U W V" using `bet U W V` .
	have "ang_lt A B C P Q R" using anglelessthan_b[OF `bet U W V` `ray_on Q P U` `ray_on Q R V` `ang_eq A B C P Q W`] .
	thus ?thesis by blast
qed

end