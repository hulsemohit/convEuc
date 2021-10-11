theory ABCequalsCBA
	imports Geometry collinearorder congruencesymmetric congruencetransitive doublereverse equalitysymmetric inequalitysymmetric ray4 sumofparts
begin

theorem(in euclidean_geometry) ABCequalsCBA:
	assumes 
		"\<not> col A B C"
	shows "ang_eq A B C C B A"
proof -
	have "\<not> (B = A)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> A)"
		hence "B = A" by blast
		have "A = B" using equalitysymmetric[OF `B = A`] .
		have "col A B C" using collinear_b `A = B` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> A" by blast
	have "\<not> (C = B)"
	proof (rule ccontr)
		assume "\<not> (C \<noteq> B)"
		hence "C = B" by blast
		have "col C B A" using collinear_b `C = B` by blast
		have "col A B C" using collinearorder[OF `col C B A`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "C \<noteq> B" by blast
	obtain E where "bet B A E \<and> seg_eq A E C B" using extensionE[OF `B \<noteq> A` `C \<noteq> B`]  by  blast
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> C)"
		hence "B = C" by blast
		have "col A B C" using collinear_b `B = C` by blast
		have "\<not> col A B C" using `\<not> col A B C` .
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "A \<noteq> B" using inequalitysymmetric[OF `B \<noteq> A`] .
	obtain F where "bet B C F \<and> seg_eq C F A B" using extensionE[OF `B \<noteq> C` `A \<noteq> B`]  by  blast
	have "bet B C F" using `bet B C F \<and> seg_eq C F A B` by blast
	have "seg_eq C F A B" using `bet B C F \<and> seg_eq C F A B` by blast
	have "seg_eq B A F C" using doublereverse[OF `seg_eq C F A B`] by blast
	have "seg_eq A E C B" using `bet B A E \<and> seg_eq A E C B` by blast
	have "bet B A E" using `bet B A E \<and> seg_eq A E C B` by blast
	have "bet F C B" using betweennesssymmetryE[OF `bet B C F`] .
	have "seg_eq B E F B" using sumofparts[OF `seg_eq B A F C` `seg_eq A E C B` `bet B A E` `bet F C B`] .
	have "seg_eq F B B F" using equalityreverseE.
	have "seg_eq B E B F" using congruencetransitive[OF `seg_eq B E F B` `seg_eq F B B F`] .
	have "seg_eq B F B E" using congruencesymmetric[OF `seg_eq B E B F`] .
	have "seg_eq E F F E" using equalityreverseE.
	have "ray_on B A E" using ray4 `bet B A E \<and> seg_eq A E C B` `B \<noteq> A` by blast
	have "ray_on B C F" using ray4 `bet B C F \<and> seg_eq C F A B` `B \<noteq> C` by blast
	have "ang_eq A B C C B A" using equalangles_b[OF `ray_on B A E` `ray_on B C F` `ray_on B C F` `ray_on B A E` `seg_eq B E B F` `seg_eq B F B E` `seg_eq E F F E` `\<not> col A B C`] .
	thus ?thesis by blast
qed

end