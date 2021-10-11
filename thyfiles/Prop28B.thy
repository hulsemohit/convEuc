theory Prop28B
	imports ABCequalsCBA Geometry Prop27 angledistinct collinearorder equalanglesNC equalanglessymmetric equalanglestransitive oppositesidesymmetric planeseparation ray4 samesidesymmetric supplements supplementsymmetric
begin

theorem(in euclidean_geometry) Prop28B:
	assumes 
		"bet A G B"
		"bet C H D"
		"ang_sum_right B G H G H D"
		"same_side B D G H"
	shows "parallel A B C D"
proof -
	have "same_side D B G H" using samesidesymmetric[OF `same_side B D G H`] by blast
	obtain a b c d e where "supplement a b c e d \<and> ang_eq B G H a b c \<and> ang_eq G H D e b d" using tworightangles_f[OF `ang_sum_right B G H G H D`]  by  blast
	have "supplement a b c e d" using `supplement a b c e d \<and> ang_eq B G H a b c \<and> ang_eq G H D e b d` by blast
	have "ang_eq B G H a b c" using `supplement a b c e d \<and> ang_eq B G H a b c \<and> ang_eq G H D e b d` by blast
	have "ang_eq G H D e b d" using `supplement a b c e d \<and> ang_eq B G H a b c \<and> ang_eq G H D e b d` by blast
	have "ang_eq a b c B G H" using equalanglessymmetric[OF `ang_eq B G H a b c`] .
	have "G \<noteq> H" using angledistinct[OF `ang_eq B G H a b c`] by blast
	have "ang_eq e b d G H D" using equalanglessymmetric[OF `ang_eq G H D e b d`] .
	have "H = H" using equalityreflexiveE.
	have "ray_on G H H" using ray4 `H = H` `G \<noteq> H` by blast
	have "supplement A G H H B" using supplement_b[OF `ray_on G H H` `bet A G B`] .
	have "supplement B G H H A" using supplementsymmetric[OF `supplement A G H H B`] .
	have "ang_eq e b d H G A" using supplements[OF `ang_eq a b c B G H` `supplement a b c e d` `supplement B G H H A`] .
	have "ang_eq G H D e b d" using equalanglessymmetric[OF `ang_eq e b d G H D`] .
	have "ang_eq G H D H G A" using equalanglestransitive[OF `ang_eq G H D e b d` `ang_eq e b d H G A`] .
	have "\<not> col H G A" using equalanglesNC[OF `ang_eq G H D H G A`] .
	have "ang_eq H G A A G H" using ABCequalsCBA[OF `\<not> col H G A`] .
	have "ang_eq G H D A G H" using equalanglestransitive[OF `ang_eq G H D H G A` `ang_eq H G A A G H`] .
	have "ang_eq A G H G H D" using equalanglessymmetric[OF `ang_eq G H D A G H`] .
	have "G = G" using equalityreflexiveE.
	have "col G H G" using collinear_b `G = G` by blast
	have "\<not> col A G H" using equalanglesNC[OF `ang_eq G H D A G H`] .
	have "\<not> (col G H A)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col G H A))"
hence "col G H A" by blast
		have "col A G H" using collinearorder[OF `col G H A`] by blast
		show "False" using `col A G H` `\<not> col A G H` by blast
	qed
	hence "\<not> col G H A" by blast
	have "oppo_side A G H B" using oppositeside_b[OF `bet A G B` `col G H G` `\<not> col G H A`] .
	have "oppo_side B G H A" using oppositesidesymmetric[OF `oppo_side A G H B`] .
	have "oppo_side D G H A" using planeseparation[OF `same_side D B G H` `oppo_side B G H A`] .
	have "oppo_side A G H D" using oppositesidesymmetric[OF `oppo_side D G H A`] .
	have "parallel A B C D" using Prop27[OF `bet A G B` `bet C H D` `ang_eq A G H G H D` `oppo_side A G H D`] .
	thus ?thesis by blast
qed

end