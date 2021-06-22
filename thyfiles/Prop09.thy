theory Prop09
	imports Axioms Definitions Theorems
begin

theorem Prop09:
	assumes: `axioms`
		"\<not> col B A C"
	shows: "\<exists> F. ang_eq B A F F A C \<and> ang_in B A C F"
proof -
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "A = B"
		have "B = A" using equalitysymmetric[OF `axioms` `A = B`] .
		have "col B A C" using collinear_b `axioms` `B = A` by blast
		show "False" using `col B A C` `\<not> col B A C` by blast
	qed
	hence "A \<noteq> B" by blast
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "A = C"
		have "col B A C" using collinear_b `axioms` `A = C` by blast
		show "False" using `col B A C` `\<not> col B A C` by blast
	qed
	hence "A \<noteq> C" by blast
	obtain E where "ray_on A C E \<and> seg_eq A E A B" using layoff[OF `axioms` `A \<noteq> C` `A \<noteq> B`] by blast
	have "ray_on A C E" using `ray_on A C E \<and> seg_eq A E A B` by blast
	have "seg_eq A E A B" using `ray_on A C E \<and> seg_eq A E A B` by blast
	have "\<not> (B = E)"
	proof (rule ccontr)
		assume "B = E"
		have "col A B E" using collinear_b `axioms` `B = E` by blast
		have "col A C E" using rayimpliescollinear[OF `axioms` `ray_on A C E`] .
		have "col E A B" using collinearorder[OF `axioms` `col A B E`] by blast
		have "col E A C" using collinearorder[OF `axioms` `col A C E`] by blast
		have "A \<noteq> E" using raystrict[OF `axioms` `ray_on A C E`] .
		have "E \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> E`] .
		have "col A B C" using collinear4[OF `axioms` `col E A B` `col E A C` `E \<noteq> A`] .
		have "col B A C" using collinearorder[OF `axioms` `col A B C`] by blast
		show "False" using `col B A C` `\<not> col B A C` by blast
	qed
	hence "B \<noteq> E" by blast
	obtain F where "bet B F E \<and> seg_eq F B F E" using Prop10[OF `axioms` `B \<noteq> E`] by blast
	have "bet B F E" using `bet B F E \<and> seg_eq F B F E` by blast
	have "seg_eq F B F E" using `bet B F E \<and> seg_eq F B F E` by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "F = F" using equalityreflexiveE[OF `axioms`] .
	have "seg_eq A F A F" using congruencereflexiveE[OF `axioms`] by blast
	have "seg_eq A B A E" using congruencesymmetric[OF `axioms` `seg_eq A E A B`] .
	have "seg_eq E F B F" using doublereverse[OF `axioms` `seg_eq F B F E`] by blast
	have "seg_eq B F E F" using congruencesymmetric[OF `axioms` `seg_eq E F B F`] .
	have "\<not> (col B A F)"
	proof (rule ccontr)
		assume "col B A F"
		have "col B F E" using collinear_b `axioms` `bet B F E \<and> seg_eq F B F E` by blast
		have "col F B E" using collinearorder[OF `axioms` `col B F E`] by blast
		have "col F B A" using collinearorder[OF `axioms` `col B A F`] by blast
		have "B \<noteq> F" using betweennotequal[OF `axioms` `bet B F E`] by blast
		have "F \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> F`] .
		have "col B E A" using collinear4[OF `axioms` `col F B E` `col F B A` `F \<noteq> B`] .
		have "col A C E" using rayimpliescollinear[OF `axioms` `ray_on A C E`] .
		have "col E A B" using collinearorder[OF `axioms` `col B E A`] by blast
		have "col E A C" using collinearorder[OF `axioms` `col A C E`] by blast
		have "A \<noteq> E" using raystrict[OF `axioms` `ray_on A C E`] .
		have "E \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> E`] .
		have "col A B C" using collinear4[OF `axioms` `col E A B` `col E A C` `E \<noteq> A`] .
		have "col B A C" using collinearorder[OF `axioms` `col A B C`] by blast
		show "False" using `col B A C` `\<not> col B A C` by blast
	qed
	hence "\<not> col B A F" by blast
	have "ray_on A B B" using ray4 `axioms` `B = B` `A \<noteq> B` by blast
	have "\<not> (A = F)"
	proof (rule ccontr)
		assume "A = F"
		have "col B A F" using collinear_b `axioms` `A = F` by blast
		show "False" using `col B A F` `\<not> col B A F` by blast
	qed
	hence "A \<noteq> F" by blast
	have "ray_on A F F" using ray4 `axioms` `F = F` `A \<noteq> F` by blast
	have "ray_on A C E" using `ray_on A C E` .
	have "ang_eq B A F C A F" using equalangles_b[OF `axioms` `ray_on A B B` `ray_on A F F` `ray_on A C E` `ray_on A F F` `seg_eq A B A E` `seg_eq A F A F` `seg_eq B F E F` `\<not> col B A F`] .
	have "ang_eq C A F B A F" using equalanglessymmetric[OF `axioms` `ang_eq B A F C A F`] .
	have "\<not> col C A F" using equalangles_f[OF `axioms` `ang_eq C A F B A F`] by blast
	have "ang_eq C A F F A C" using ABCequalsCBA[OF `axioms` `\<not> col C A F`] .
	have "ang_eq B A F F A C" using equalanglestransitive[OF `axioms` `ang_eq B A F C A F` `ang_eq C A F F A C`] .
	have "ang_in B A C F" using interior_b[OF `axioms` `ray_on A B B` `ray_on A C E` `bet B F E`] .
	have "ang_eq B A F F A C \<and> ang_in B A C F" using `ang_eq B A F F A C` `ang_in B A C F` by blast
	thus ?thesis by blast
qed

end