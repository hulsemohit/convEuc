theory Prop09
	imports ABCequalsCBA Geometry Prop10 betweennotequal collinear4 collinearorder congruencesymmetric doublereverse equalanglessymmetric equalanglestransitive equalitysymmetric inequalitysymmetric layoff ray4 rayimpliescollinear raystrict
begin

theorem(in euclidean_geometry) Prop09:
	assumes 
		"\<not> col B A C"
	shows "\<exists> F. ang_eq B A F F A C \<and> ang_in B A C F"
proof -
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> B)"
		hence "A = B" by blast
		have "B = A" using equalitysymmetric[OF `A = B`] .
		have "col B A C" using collinear_b `B = A` by blast
		show "False" using `col B A C` `\<not> col B A C` by blast
	qed
	hence "A \<noteq> B" by blast
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> C)"
		hence "A = C" by blast
		have "col B A C" using collinear_b `A = C` by blast
		show "False" using `col B A C` `\<not> col B A C` by blast
	qed
	hence "A \<noteq> C" by blast
	obtain E where "ray_on A C E \<and> seg_eq A E A B" using layoff[OF `A \<noteq> C` `A \<noteq> B`]  by  blast
	have "ray_on A C E" using `ray_on A C E \<and> seg_eq A E A B` by blast
	have "seg_eq A E A B" using `ray_on A C E \<and> seg_eq A E A B` by blast
	have "\<not> (B = E)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> E)"
		hence "B = E" by blast
		have "col A B E" using collinear_b `B = E` by blast
		have "col A C E" using rayimpliescollinear[OF `ray_on A C E`] .
		have "col E A B" using collinearorder[OF `col A B E`] by blast
		have "col E A C" using collinearorder[OF `col A C E`] by blast
		have "A \<noteq> E" using raystrict[OF `ray_on A C E`] .
		have "E \<noteq> A" using inequalitysymmetric[OF `A \<noteq> E`] .
		have "col A B C" using collinear4[OF `col E A B` `col E A C` `E \<noteq> A`] .
		have "col B A C" using collinearorder[OF `col A B C`] by blast
		show "False" using `col B A C` `\<not> col B A C` by blast
	qed
	hence "B \<noteq> E" by blast
	obtain F where "bet B F E \<and> seg_eq F B F E" using Prop10[OF `B \<noteq> E`]  by  blast
	have "bet B F E" using `bet B F E \<and> seg_eq F B F E` by blast
	have "seg_eq F B F E" using `bet B F E \<and> seg_eq F B F E` by blast
	have "B = B" using equalityreflexiveE.
	have "F = F" using equalityreflexiveE.
	have "seg_eq A F A F" using congruencereflexiveE.
	have "seg_eq A B A E" using congruencesymmetric[OF `seg_eq A E A B`] .
	have "seg_eq E F B F" using doublereverse[OF `seg_eq F B F E`] by blast
	have "seg_eq B F E F" using congruencesymmetric[OF `seg_eq E F B F`] .
	have "\<not> (col B A F)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B A F))"
hence "col B A F" by blast
		have "col B F E" using collinear_b `bet B F E \<and> seg_eq F B F E` by blast
		have "col F B E" using collinearorder[OF `col B F E`] by blast
		have "col F B A" using collinearorder[OF `col B A F`] by blast
		have "B \<noteq> F" using betweennotequal[OF `bet B F E`] by blast
		have "F \<noteq> B" using inequalitysymmetric[OF `B \<noteq> F`] .
		have "col B E A" using collinear4[OF `col F B E` `col F B A` `F \<noteq> B`] .
		have "col A C E" using rayimpliescollinear[OF `ray_on A C E`] .
		have "col E A B" using collinearorder[OF `col B E A`] by blast
		have "col E A C" using collinearorder[OF `col A C E`] by blast
		have "A \<noteq> E" using raystrict[OF `ray_on A C E`] .
		have "E \<noteq> A" using inequalitysymmetric[OF `A \<noteq> E`] .
		have "col A B C" using collinear4[OF `col E A B` `col E A C` `E \<noteq> A`] .
		have "col B A C" using collinearorder[OF `col A B C`] by blast
		show "False" using `col B A C` `\<not> col B A C` by blast
	qed
	hence "\<not> col B A F" by blast
	have "ray_on A B B" using ray4 `B = B` `A \<noteq> B` by blast
	have "\<not> (A = F)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> F)"
		hence "A = F" by blast
		have "col B A F" using collinear_b `A = F` by blast
		show "False" using `col B A F` `\<not> col B A F` by blast
	qed
	hence "A \<noteq> F" by blast
	have "ray_on A F F" using ray4 `F = F` `A \<noteq> F` by blast
	have "ray_on A C E" using `ray_on A C E` .
	have "ang_eq B A F C A F" using equalangles_b[OF `ray_on A B B` `ray_on A F F` `ray_on A C E` `ray_on A F F` `seg_eq A B A E` `seg_eq A F A F` `seg_eq B F E F` `\<not> col B A F`] .
	have "ang_eq C A F B A F" using equalanglessymmetric[OF `ang_eq B A F C A F`] .
	have "\<not> col C A F" using equalangles_f[OF `ang_eq C A F B A F`] by blast
	have "ang_eq C A F F A C" using ABCequalsCBA[OF `\<not> col C A F`] .
	have "ang_eq B A F F A C" using equalanglestransitive[OF `ang_eq B A F C A F` `ang_eq C A F F A C`] .
	have "ang_in B A C F" using interior_b[OF `ray_on A B B` `ray_on A C E` `bet B F E`] .
	have "ang_eq B A F F A C \<and> ang_in B A C F" using `ang_eq B A F F A C` `ang_in B A C F` by blast
	thus ?thesis by blast
qed

end