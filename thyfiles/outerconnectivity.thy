theory outerconnectivity
	imports Axioms Definitions Theorems
begin

theorem outerconnectivity:
	assumes: `axioms`
		"bet A B C"
		"bet A B D"
		"\<not> (bet B C D)"
		"\<not> (bet B D C)"
	shows: "C = D"
proof -
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "A = C"
		have "bet A B A" using `bet A B C` `A = C` by blast
		have "\<not> (bet A B A)" using betweennessidentityE[OF `axioms`] by blast
		show "False" using `\<not> (bet A B A)` `bet A B A` by blast
	qed
	hence "A \<noteq> C" by blast
	have "A \<noteq> D" using betweennotequal[OF `axioms` `bet A B D`] by blast
	obtain E where "bet A C E \<and> seg_eq C E A D" using extensionE[OF `axioms` `A \<noteq> C` `A \<noteq> D`] by blast
	have "bet A C E" using `bet A C E \<and> seg_eq C E A D` by blast
	have "bet A B E" using n3_6b[OF `axioms` `bet A B C` `bet A C E`] .
	have "\<not> (A = D)"
	proof (rule ccontr)
		assume "A = D"
		have "bet A B A" using `bet A B D` `A = D` by blast
		have "\<not> (bet A B A)" using betweennessidentityE[OF `axioms`] by blast
		show "False" using `\<not> (bet A B A)` `bet A B A` by blast
	qed
	hence "A \<noteq> D" by blast
	have "A \<noteq> C" using betweennotequal[OF `axioms` `bet A B C`] by blast
	obtain F where "bet A D F \<and> seg_eq D F A C" using extensionE[OF `axioms` `A \<noteq> D` `A \<noteq> C`] by blast
	have "bet A D F" using `bet A D F \<and> seg_eq D F A C` by blast
	have "bet A B D" using `bet A B D` .
	have "bet F D A" using betweennesssymmetryE[OF `axioms` `bet A D F`] .
	have "bet D B A" using betweennesssymmetryE[OF `axioms` `bet A B D`] .
	have "bet F B A" using n3_5b[OF `axioms` `bet F D A` `bet D B A`] .
	have "bet A B F" using betweennesssymmetryE[OF `axioms` `bet F B A`] .
	have "seg_eq D F A C" using `bet A D F \<and> seg_eq D F A C` by blast
	have "seg_eq F D D F" using equalityreverseE[OF `axioms`] by blast
	have "seg_eq F D A C" using congruencetransitive[OF `axioms` `seg_eq F D D F` `seg_eq D F A C`] .
	have "seg_eq C E A D" using `bet A C E \<and> seg_eq C E A D` by blast
	have "seg_eq A D C E" using congruencesymmetric[OF `axioms` `seg_eq C E A D`] .
	have "seg_eq D A A D" using equalityreverseE[OF `axioms`] by blast
	have "seg_eq D A C E" using congruencetransitive[OF `axioms` `seg_eq D A A D` `seg_eq A D C E`] .
	have "seg_eq F A A E" using sumofparts[OF `axioms` `seg_eq F D A C` `seg_eq D A C E` `bet F D A` `bet A C E`] .
	have "seg_eq A E F A" using congruencesymmetric[OF `axioms` `seg_eq F A A E`] .
	have "seg_eq F A A F" using equalityreverseE[OF `axioms`] by blast
	have "seg_eq A E A F" using congruencetransitive[OF `axioms` `seg_eq A E F A` `seg_eq F A A F`] .
	have "seg_eq A B A B" using congruencereflexiveE[OF `axioms`] by blast
	have "seg_eq B E B F" using differenceofparts[OF `axioms` `seg_eq A B A B` `seg_eq A E A F` `bet A B E` `bet A B F`] .
	have "bet A B F" using `bet A B F` .
	have "bet A B E" using `bet A B E` .
	have "seg_eq B E B F" using `seg_eq B E B F` .
	have "E = F" using extensionunique[OF `axioms` `bet A B E` `bet A B F` `seg_eq B E B F`] .
	have "bet A C E" using `bet A C E` .
	have "bet A D E" using `bet A D F` `E = F` by blast
	have "bet A B C" using `bet A B C` .
	have "bet A B D" using `bet A B D` .
	have "bet B C E" using n3_6a[OF `axioms` `bet A B C` `bet A C E`] .
	have "bet B D E" using n3_6a[OF `axioms` `bet A B D` `bet A D E`] .
	have "C = D" using connectivityE[OF `axioms` `bet B C E` `bet B D E` `\<not> (bet B C D)` `\<not> (bet B D C)`] .
	thus ?thesis by blast
qed

end