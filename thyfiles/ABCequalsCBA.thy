theory ABCequalsCBA
	imports Axioms Definitions Theorems
begin

theorem ABCequalsCBA:
	assumes: `axioms`
		"\<not> col A B C"
	shows: "ang_eq A B C C B A"
proof -
	have "\<not> (B = A)"
	proof (rule ccontr)
		assume "B = A"
		have "A = B" using equalitysymmetric[OF `axioms` `B = A`] .
		have "col A B C" using col_b `axioms` `A = B` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> A" by blast
	have "\<not> (C = B)"
	proof (rule ccontr)
		assume "C = B"
		have "col C B A" using col_b `axioms` `C = B` by blast
		have "col A B C" using collinearorder[OF `axioms` `col C B A`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "C \<noteq> B" by blast
	obtain E where "bet B A E \<and> seg_eq A E C B" using extensionE[OF `axioms` `B \<noteq> A` `C \<noteq> B`]  by  blast
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "B = C"
		have "col A B C" using col_b `axioms` `B = C` by blast
		have "\<not> col A B C" using `\<not> col A B C` .
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "A \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> A`] .
	obtain F where "bet B C F \<and> seg_eq C F A B" using extensionE[OF `axioms` `B \<noteq> C` `A \<noteq> B`]  by  blast
	have "bet B C F" using `bet B C F \<and> seg_eq C F A B` by blast
	have "seg_eq C F A B" using `bet B C F \<and> seg_eq C F A B` by blast
	have "seg_eq B A F C" using doublereverse[OF `axioms` `seg_eq C F A B`] by blast
	have "seg_eq A E C B" using `bet B A E \<and> seg_eq A E C B` by blast
	have "bet B A E" using `bet B A E \<and> seg_eq A E C B` by blast
	have "bet F C B" using betweennesssymmetryE[OF `axioms` `bet B C F`] .
	have "seg_eq B E F B" using sumofparts[OF `axioms` `seg_eq B A F C` `seg_eq A E C B` `bet B A E` `bet F C B`] .
	have "seg_eq F B B F" using equalityreverseE[OF `axioms`] .
	have "seg_eq B E B F" using congruencetransitive[OF `axioms` `seg_eq B E F B` `seg_eq F B B F`] .
	have "seg_eq B F B E" using congruencesymmetric[OF `axioms` `seg_eq B E B F`] .
	have "seg_eq E F F E" using equalityreverseE[OF `axioms`] .
	have "ray_on B A E" using ray4 `axioms` `bet B A E \<and> seg_eq A E C B` `B \<noteq> A` by blast
	have "ray_on B C F" using ray4 `axioms` `bet B C F \<and> seg_eq C F A B` `B \<noteq> C` by blast
	have "ang_eq A B C C B A" sorry
	thus ?thesis by blast
qed

end