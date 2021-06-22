theory Prop01
	imports Axioms Definitions Theorems
begin

theorem Prop01:
	assumes: `axioms`
		"A \<noteq> B"
	shows: "\<exists> C. equilateral A B C \<and> triangle A B C"
proof -
	obtain J where "circle J A A B" using circle_f[OF `axioms` `A \<noteq> B`] by blast
	obtain K where "circle K B A B" using circle_f[OF `axioms` `A \<noteq> B`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	obtain D where "bet B A D \<and> seg_eq A D A B" using extensionE[OF `axioms` `B \<noteq> A` `A \<noteq> B`] by blast
	have "bet B A D" using `bet B A D \<and> seg_eq A D A B` by blast
	have "seg_eq A D A B" using `bet B A D \<and> seg_eq A D A B` by blast
	have "seg_eq B A A B" using equalityreverseE[OF `axioms`] by blast
	have "circle K B A B \<and> cir_ou D K" using outside_b[OF `axioms` `circle K B A B` `bet B A D` `seg_eq B A A B`] .
	have "cir_ou D K" using `circle K B A B \<and> cir_ou D K` by blast
	obtain E where "bet A B E \<and> seg_eq B E A B" using extensionE[OF `axioms` `A \<noteq> B` `A \<noteq> B`] by blast
	have "bet A B E" using `bet A B E \<and> seg_eq B E A B` by blast
	have "seg_eq B E A B" using `bet A B E \<and> seg_eq B E A B` by blast
	have "seg_eq B A A B" using equalityreverseE[OF `axioms`] by blast
	have "circle K B A B \<and> cir_in B K" using inside_b[OF `axioms` `circle K B A B` `bet A B E` `seg_eq B E A B` `seg_eq B A A B` `bet A B E`] .
	have "cir_in B K" using `circle K B A B \<and> cir_in B K` by blast
	have "circle J A A B \<and> cir_on D J" using on_b[OF `axioms` `circle J A A B` `seg_eq A D A B`] .
	have "cir_on D J" using `circle J A A B \<and> cir_on D J` by blast
	have "seg_eq A B A B" using congruencereflexiveE[OF `axioms`] by blast
	have "circle J A A B \<and> cir_on B J" using on_b[OF `axioms` `circle J A A B` `seg_eq A B A B`] .
	have "cir_on B J" using `circle J A A B \<and> cir_on B J` by blast
	obtain C where "cir_on C K \<and> cir_on C J" using circle-circleE[OF `axioms` `circle K B A B` `cir_in B K` `cir_ou D K` `circle J A A B` `cir_on B J` `cir_on D J`] by blast
	have "cir_on C J" using `cir_on C K \<and> cir_on C J` by blast
	have "cir_on C K" using `cir_on C K \<and> cir_on C J` by blast
	have "seg_eq A C A B" using on_f[OF `axioms` `circle J A A B` `cir_on C J`] by blast
	have "seg_eq A B A C" using congruencesymmetric[OF `axioms` `seg_eq A C A B`] .
	have "seg_eq B C A B" using on_f[OF `axioms` `circle K B A B` `cir_on C K`] by blast
	have "seg_eq B C A C" using congruencetransitive[OF `axioms` `seg_eq B C A B` `seg_eq A B A C`] .
	have "seg_eq A B B C" using congruencesymmetric[OF `axioms` `seg_eq B C A B`] .
	have "seg_eq A C C A" using equalityreverseE[OF `axioms`] by blast
	have "seg_eq B C C A" using congruencetransitive[OF `axioms` `seg_eq B C A C` `seg_eq A C C A`] .
	have "equilateral A B C" using equilateral_b[OF `axioms` `seg_eq A B B C` `seg_eq B C C A`] .
	have "A \<noteq> B" using `A \<noteq> B` .
	have "seg_eq A B B C" using `seg_eq A B B C` .
	have "B \<noteq> C" using nullsegment3[OF `axioms` `A \<noteq> B` `seg_eq A B B C`] .
	have "seg_eq B C C A" using `seg_eq B C C A` .
	have "C \<noteq> A" using nullsegment3[OF `axioms` `B \<noteq> C` `seg_eq B C C A`] .
	have "\<not> (bet A C B)"
	proof (rule ccontr)
		assume "bet A C B"
		have "\<not> (seg_eq A C A B)" using partnotequalwhole[OF `axioms` `bet A C B`] .
		have "seg_eq A C A B" using `seg_eq A C A B` .
		have "seg_eq C A A C" using equalityreverseE[OF `axioms`] by blast
		have "seg_eq C A A B" using congruencetransitive[OF `axioms` `seg_eq C A A C` `seg_eq A C A B`] .
		have "seg_eq A C C A" using equalityreverseE[OF `axioms`] by blast
		have "seg_eq A C A B" using congruencetransitive[OF `axioms` `seg_eq A C A B` `seg_eq A B A B`] .
		show "False" using `seg_eq A C A B` `\<not> (seg_eq A C A B)` by blast
	qed
	hence "\<not> (bet A C B)" by blast
	have "\<not> (bet A B C)"
	proof (rule ccontr)
		assume "bet A B C"
		have "\<not> (seg_eq A B A C)" using partnotequalwhole[OF `axioms` `bet A B C`] .
		have "seg_eq A B C A" using congruencetransitive[OF `axioms` `seg_eq A B A C` `seg_eq A C C A`] .
		have "seg_eq C A A C" using equalityreverseE[OF `axioms`] by blast
		have "seg_eq A B A C" using congruencetransitive[OF `axioms` `seg_eq A B A B` `seg_eq A B A C`] .
		show "False" using `seg_eq A B A C` `\<not> (seg_eq A B A C)` by blast
	qed
	hence "\<not> (bet A B C)" by blast
	have "\<not> (bet B A C)"
	proof (rule ccontr)
		assume "bet B A C"
		have "\<not> (seg_eq B A B C)" using partnotequalwhole[OF `axioms` `bet B A C`] .
		have "seg_eq A B B C" using `seg_eq A B B C` .
		have "seg_eq B A A B" using equalityreverseE[OF `axioms`] by blast
		have "seg_eq B A B C" using congruencetransitive[OF `axioms` `seg_eq B A A B` `seg_eq A B B C`] .
		show "False" using `seg_eq B A B C` `\<not> (seg_eq B A B C)` by blast
	qed
	hence "\<not> (bet B A C)" by blast
	have "\<not> (col A B C)"
	proof (rule ccontr)
		assume "col A B C"
		have "A \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> A`] .
		have "A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C \<and> \<not> (bet B A C) \<and> \<not> (bet A B C) \<and> \<not> (bet A C B)" using `A \<noteq> B` `A \<noteq> C` `B \<noteq> C` `\<not> (bet B A C)` `\<not> (bet A B C)` `\<not> (bet A C B)` by blast
		have "A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B" using collinear_f[OF `axioms` `col A B C`] .
		show "False" using `A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B` `A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C \<and> \<not> (bet B A C) \<and> \<not> (bet A B C) \<and> \<not> (bet A C B)` by blast
	qed
	hence "\<not> col A B C" by blast
	have "triangle A B C" using triangle_b[OF `axioms` `\<not> col A B C`] .
	have "equilateral A B C \<and> triangle A B C" using `equilateral A B C` `triangle A B C` by blast
	thus ?thesis by blast
qed

end