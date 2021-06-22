theory layoffunique
	imports Axioms Definitions Theorems
begin

theorem layoffunique:
	assumes: `axioms`
		"ray_on A B C"
		"ray_on A B D"
		"seg_eq A C A D"
	shows: "C = D"
proof -
	have "seg_eq A D A C" using congruencesymmetric[OF `axioms` `seg_eq A C A D`] .
	have "bet A C B \<or> B = C \<or> bet A B C" using ray1[OF `axioms` `ray_on A B C`] .
	have "bet A D B \<or> B = D \<or> bet A B D" using ray1[OF `axioms` `ray_on A B D`] .
	have "seg_eq A B A B" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq C B C B" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq A C A C" using congruencereflexiveE[OF `axioms`] .
	consider "bet A C B"|"B = C"|"bet A B C" using `bet A C B \<or> B = C \<or> bet A B C`  by blast
	hence C = D
	proof (cases)
		case 1
		consider "bet A D B"|"B = D"|"bet A B D" using `bet A D B \<or> B = D \<or> bet A B D`  by blast
		hence C = D
		proof (cases)
			case 1
			have "seg_eq C B D B" using differenceofparts[OF `axioms` `seg_eq A C A D` `seg_eq A B A B` `bet A C B` `bet A D B`] .
			have "seg_eq B C B D" using congruenceflip[OF `axioms` `seg_eq C B D B`] by blast
			have "seg_eq C C C D" using interior5[OF `axioms` `bet A C B` `bet A C B` `seg_eq A C A C` `seg_eq C B C B` `seg_eq A C A D` `seg_eq B C B D`] .
			have "seg_eq C D C C" using congruencesymmetric[OF `axioms` `seg_eq C C C D`] .
			have "\<not> (C \<noteq> D)"
			proof (rule ccontr)
				assume "C \<noteq> D"
				have "C \<noteq> C" using nullsegment3[OF `axioms` `C \<noteq> D` `seg_eq C D C C`] .
				have "C = C" using equalityreflexiveE[OF `axioms`] .
				show "False" using `C = C` `C \<noteq> C` by blast
			qed
			hence "C = D" by blast
		next
			case 2
			have "bet A C D" sorry
			have "\<not> (C \<noteq> D)"
			proof (rule ccontr)
				assume "C \<noteq> D"
				have "\<not> (seg_eq A C A D)" using partnotequalwhole[OF `axioms` `bet A C D`] .
				show "False" using `\<not> (seg_eq A C A D)` `seg_eq A C A D` by blast
			qed
			hence "C = D" by blast
		next
			case 3
			have "bet A C D" using n3_6b[OF `axioms` `bet A C B` `bet A B D`] .
			have "\<not> (C \<noteq> D)"
			proof (rule ccontr)
				assume "C \<noteq> D"
				have "\<not> (seg_eq A C A D)" using partnotequalwhole[OF `axioms` `bet A C D`] .
				show "False" using `\<not> (seg_eq A C A D)` `seg_eq A C A D` by blast
			qed
			hence "C = D" by blast
		next
	next
		case 2
		have "seg_eq A B A D" sorry
		have "seg_eq A D A B" using congruencesymmetric[OF `axioms` `seg_eq A B A D`] .
		consider "bet A D B"|"B = D"|"bet A B D" using `bet A D B \<or> B = D \<or> bet A B D`  by blast
		hence C = D
		proof (cases)
			case 1
			have "\<not> (C \<noteq> D)"
			proof (rule ccontr)
				assume "C \<noteq> D"
				have "\<not> (seg_eq A D A B)" using partnotequalwhole[OF `axioms` `bet A D B`] .
				show "False" using `\<not> (seg_eq A D A B)` `seg_eq A D A B` by blast
			qed
			hence "C = D" by blast
		next
			case 2
			have "C = B" using equalitysymmetric[OF `axioms` `B = C`] .
			have "D = B" using equalitysymmetric[OF `axioms` `B = D`] .
			have "C = D" using equalitytransitiveE[OF `axioms` `C = B` `D = B`] .
		next
			case 3
			have "bet A C D" sorry
			have "\<not> (C \<noteq> D)"
			proof (rule ccontr)
				assume "C \<noteq> D"
				have "\<not> (seg_eq A C A D)" using partnotequalwhole[OF `axioms` `bet A C D`] .
				show "False" using `\<not> (seg_eq A C A D)` `seg_eq A C A D` by blast
			qed
			hence "C = D" by blast
		next
	next
		case 3
		consider "bet A D B"|"B = D"|"bet A B D" using `bet A D B \<or> B = D \<or> bet A B D`  by blast
		hence C = D
		proof (cases)
			case 1
			have "bet A D C" using n3_6b[OF `axioms` `bet A D B` `bet A B C`] .
			have "\<not> (C \<noteq> D)"
			proof (rule ccontr)
				assume "C \<noteq> D"
				have "\<not> (seg_eq A D A C)" using partnotequalwhole[OF `axioms` `bet A D C`] .
				show "False" using `\<not> (seg_eq A D A C)` `seg_eq A D A C` by blast
			qed
			hence "C = D" by blast
		next
			case 2
			have "bet A D C" sorry
			have "\<not> (C \<noteq> D)"
			proof (rule ccontr)
				assume "C \<noteq> D"
				have "\<not> (seg_eq A D A C)" using partnotequalwhole[OF `axioms` `bet A D C`] .
				show "False" using `\<not> (seg_eq A D A C)` `seg_eq A D A C` by blast
			qed
			hence "C = D" by blast
		next
			case 3
			have "seg_eq B C B D" using differenceofparts[OF `axioms` `seg_eq A B A B` `seg_eq A C A D` `bet A B C` `bet A B D`] .
			have "C = D" using extensionunique[OF `axioms` `bet A B C` `bet A B D` `seg_eq B C B D`] .
		next
	next
	thus ?thesis by blast
qed

end