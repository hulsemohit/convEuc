theory insideor
	imports Axioms Definitions Theorems
begin

theorem insideor:
	assumes: `axioms`
		"circle J C P Q"
		"cir_in A J"
	shows: "A = C \<or> seg_lt C A P Q"
proof -
	obtain D E where "circle J C P Q \<and> bet D C E \<and> seg_eq C E P Q \<and> seg_eq C D P Q \<and> bet D A E" using inside_f[OF `axioms` `circle J C P Q` `cir_in A J`] by blast
	have "seg_eq C E P Q" using `circle J C P Q \<and> bet D C E \<and> seg_eq C E P Q \<and> seg_eq C D P Q \<and> bet D A E` by blast
	have "seg_eq C D P Q" using `circle J C P Q \<and> bet D C E \<and> seg_eq C E P Q \<and> seg_eq C D P Q \<and> bet D A E` by blast
	have "bet D A E" using `circle J C P Q \<and> bet D C E \<and> seg_eq C E P Q \<and> seg_eq C D P Q \<and> bet D A E` by blast
	consider "A = C"|"A \<noteq> C" by blast
	hence A = C \<or> seg_lt C A P Q
	proof (cases)
		case 1
		have "A = C \<or> seg_lt C A P Q" using `A = C` by blast
	next
		case 2
		have "seg_lt C A P Q"
		proof (rule ccontr)
			assume "\<not> (seg_lt C A P Q)"
			have "\<not> (bet D A C)"
			proof (rule ccontr)
				assume "bet D A C"
				have "bet C A D" using betweennesssymmetryE[OF `axioms` `bet D A C`] .
				have "seg_eq C A C A" using congruencereflexiveE[OF `axioms`] by blast
				have "seg_lt C A C D" using lessthan_b[OF `axioms` `bet C A D` `seg_eq C A C A`] .
				have "seg_lt C A P Q" using lessthancongruence[OF `axioms` `seg_lt C A C D` `seg_eq C D P Q`] .
				show "False" using `seg_lt C A P Q` `\<not> (seg_lt C A P Q)` by blast
			qed
			hence "\<not> (bet D A C)" by blast
			have "\<not> (bet D C A)"
			proof (rule ccontr)
				assume "bet D C A"
				have "bet C A E" using n3_6a[OF `axioms` `bet D C A` `bet D A E`] .
				have "seg_eq C A C A" using congruencereflexiveE[OF `axioms`] by blast
				have "seg_lt C A C E" using lessthan_b[OF `axioms` `bet C A E` `seg_eq C A C A`] .
				have "seg_lt C A P Q" using lessthancongruence[OF `axioms` `seg_lt C A C E` `seg_eq C E P Q`] .
				show "False" using `seg_lt C A P Q` `\<not> (seg_lt C A P Q)` by blast
			qed
			hence "\<not> (bet D C A)" by blast
			have "bet D A E" using `bet D A E` .
			have "bet D C E" using `circle J C P Q \<and> bet D C E \<and> seg_eq C E P Q \<and> seg_eq C D P Q \<and> bet D A E` by blast
			have "A = C" using connectivityE[OF `axioms` `bet D A E` `bet D C E` `\<not> (bet D A C)` `\<not> (bet D C A)`] .
			show "False" using `A = C` `A \<noteq> C` by blast
		qed
		hence "seg_lt C A P Q" by blast
		have "A = C \<or> seg_lt C A P Q" using `seg_lt C A P Q` by blast
	next
	thus ?thesis by blast
qed

end