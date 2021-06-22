theory Prop26B
	imports Axioms Definitions Theorems
begin

theorem Prop26B:
	assumes: `axioms`
		"triangle A B C"
		"triangle D E F"
		"ang_eq A B C D E F"
		"ang_eq B C A E F D"
		"seg_eq A B D E"
	shows: "seg_eq B C E F \<and> seg_eq A C D F \<and> ang_eq B A C E D F"
proof -
	have "\<not> (seg_lt E F B C)" using n26helper[OF `axioms` `triangle A B C` `ang_eq A B C D E F` `ang_eq B C A E F D` `seg_eq A B D E`] .
	have "ang_eq D E F A B C" using equalanglessymmetric[OF `axioms` `ang_eq A B C D E F`] .
	have "ang_eq E F D B C A" using equalanglessymmetric[OF `axioms` `ang_eq B C A E F D`] .
	have "seg_eq D E A B" using congruencesymmetric[OF `axioms` `seg_eq A B D E`] .
	have "\<not> (seg_lt B C E F)" using n26helper[OF `axioms` `triangle D E F` `ang_eq D E F A B C` `ang_eq E F D B C A` `seg_eq D E A B`] .
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "B = C"
		have "col A B C" using collinear_b `axioms` `B = C` by blast
		have "\<not> col A B C" using triangle_f[OF `axioms` `triangle A B C`] .
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "\<not> (E = F)"
	proof (rule ccontr)
		assume "E = F"
		have "col D E F" using collinear_b `axioms` `E = F` by blast
		have "\<not> col D E F" using triangle_f[OF `axioms` `triangle D E F`] .
		show "False" using `\<not> col D E F` `col D E F` by blast
	qed
	hence "E \<noteq> F" by blast
	have "seg_eq B C E F" using trichotomy1[OF `axioms` `\<not> (seg_lt B C E F)` `\<not> (seg_lt E F B C)` `B \<noteq> C` `E \<noteq> F`] .
	have "seg_eq B A E D" using congruenceflip[OF `axioms` `seg_eq A B D E`] by blast
	have "seg_eq A C D F \<and> ang_eq B A C E D F \<and> ang_eq B C A E F D" using Prop04[OF `axioms` `seg_eq B A E D` `seg_eq B C E F` `ang_eq A B C D E F`] .
	have "seg_eq A C D F" using `seg_eq A C D F \<and> ang_eq B A C E D F \<and> ang_eq B C A E F D` by blast
	have "ang_eq B A C E D F" using `seg_eq A C D F \<and> ang_eq B A C E D F \<and> ang_eq B C A E F D` by blast
	have "seg_eq B C E F \<and> seg_eq A C D F \<and> ang_eq B A C E D F" using `seg_eq B C E F` `seg_eq A C D F \<and> ang_eq B A C E D F \<and> ang_eq B C A E F D` `seg_eq A C D F \<and> ang_eq B A C E D F \<and> ang_eq B C A E F D` by blast
	thus ?thesis by blast
qed

end