theory triangletoparallelogram
	imports Axioms Definitions Theorems
begin

theorem triangletoparallelogram:
	assumes: `axioms`
		"parallel D C E F"
		"col E F A"
	shows: "\<exists> b. parallelogram A b C D \<and> col E F b"
proof -
	have "\<not> col D C E" using parallelNC[OF `axioms` `parallel D C E F`] by blast
	have "D \<noteq> C" using NCdistinct[OF `axioms` `\<not> col D C E`] by blast
	have "C \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> C`] .
	obtain B where "bet C D B \<and> seg_eq D B C D" using extensionE[OF `axioms` `C \<noteq> D` `C \<noteq> D`]  by  blast
	have "bet C D B" using `bet C D B \<and> seg_eq D B C D` by blast
	have "bet B D C" using betweennesssymmetryE[OF `axioms` `bet C D B`] .
	have "\<not> col C E F" using parallelNC[OF `axioms` `parallel D C E F`] by blast
	have "E \<noteq> F" using NCdistinct[OF `axioms` `\<not> col C E F`] by blast
	have "\<not> (col B C A)"
	proof (rule ccontr)
		assume "col B C A"
		have "col C D B" using col_b `axioms` `bet C D B \<and> seg_eq D B C D` by blast
		have "col B C D" using collinearorder[OF `axioms` `col C D B`] by blast
		have "B \<noteq> C" using betweennotequal[OF `axioms` `bet B D C`] by blast
		have "col C A D" using collinear4[OF `axioms` `col B C A` `col B C D` `B \<noteq> C`] .
		have "col D C A" using collinearorder[OF `axioms` `col C A D`] by blast
		have "meets D C E F" sorry
		have "\<not> (meets D C E F)" sorry
		show "False" using `\<not> (meets D C E F)` `meets D C E F` by blast
	qed
	hence "\<not> col B C A" by blast
	obtain M b c where "bet c A b \<and> ang_eq b A D A D B \<and> ang_eq b A D B D A \<and> ang_eq D A b B D A \<and> ang_eq c A D A D C \<and> ang_eq c A D C D A \<and> ang_eq D A c C D A \<and> parallel c b B C \<and> seg_eq c A D C \<and> seg_eq A b B D \<and> seg_eq A M M D \<and> seg_eq c M M C \<and> seg_eq B M M b \<and> bet c M C \<and> bet B M b \<and> bet A M D" using Prop31[OF `axioms` `bet B D C` `\<not> col B C A`]  by  blast
	have "bet c A b" using `bet c A b \<and> ang_eq b A D A D B \<and> ang_eq b A D B D A \<and> ang_eq D A b B D A \<and> ang_eq c A D A D C \<and> ang_eq c A D C D A \<and> ang_eq D A c C D A \<and> parallel c b B C \<and> seg_eq c A D C \<and> seg_eq A b B D \<and> seg_eq A M M D \<and> seg_eq c M M C \<and> seg_eq B M M b \<and> bet c M C \<and> bet B M b \<and> bet A M D` by blast
	have "parallel c b B C" using `bet c A b \<and> ang_eq b A D A D B \<and> ang_eq b A D B D A \<and> ang_eq D A b B D A \<and> ang_eq c A D A D C \<and> ang_eq c A D C D A \<and> ang_eq D A c C D A \<and> parallel c b B C \<and> seg_eq c A D C \<and> seg_eq A b B D \<and> seg_eq A M M D \<and> seg_eq c M M C \<and> seg_eq B M M b \<and> bet c M C \<and> bet B M b \<and> bet A M D` by blast
	have "bet c M C" using `bet c A b \<and> ang_eq b A D A D B \<and> ang_eq b A D B D A \<and> ang_eq D A b B D A \<and> ang_eq c A D A D C \<and> ang_eq c A D C D A \<and> ang_eq D A c C D A \<and> parallel c b B C \<and> seg_eq c A D C \<and> seg_eq A b B D \<and> seg_eq A M M D \<and> seg_eq c M M C \<and> seg_eq B M M b \<and> bet c M C \<and> bet B M b \<and> bet A M D` by blast
	have "bet B M b" using `bet c A b \<and> ang_eq b A D A D B \<and> ang_eq b A D B D A \<and> ang_eq D A b B D A \<and> ang_eq c A D A D C \<and> ang_eq c A D C D A \<and> ang_eq D A c C D A \<and> parallel c b B C \<and> seg_eq c A D C \<and> seg_eq A b B D \<and> seg_eq A M M D \<and> seg_eq c M M C \<and> seg_eq B M M b \<and> bet c M C \<and> bet B M b \<and> bet A M D` by blast
	have "bet b M B" using betweennesssymmetryE[OF `axioms` `bet B M b`] .
	have "\<not> col b B C" using parallelNC[OF `axioms` `parallel c b B C`] by blast
	obtain R where "bet b R D \<and> bet C R M" using Pasch-innerE[OF `axioms` `bet b M B` `bet C D B` `\<not> col b B C`]  by  blast
	have "bet C R M" using `bet b R D \<and> bet C R M` by blast
	have "bet C M c" using betweennesssymmetryE[OF `axioms` `bet c M C`] .
	have "bet C R c" using n3_6b[OF `axioms` `bet C R M` `bet C M c`] .
	have "bet b A c" using betweennesssymmetryE[OF `axioms` `bet c A b`] .
	have "\<not> col c b C" using parallelNC[OF `axioms` `parallel c b B C`] by blast
	have "\<not> col b c C" using NCorder[OF `axioms` `\<not> col c b C`] by blast
	obtain Q where "bet b Q R \<and> bet C Q A" using Pasch-innerE[OF `axioms` `bet b A c` `bet C R c` `\<not> col b c C`]  by  blast
	have "bet b Q R" using `bet b Q R \<and> bet C Q A` by blast
	have "bet b R D" using `bet b R D \<and> bet C R M` by blast
	have "bet b Q D" using n3_6b[OF `axioms` `bet b Q R` `bet b R D`] .
	have "bet C Q A" using `bet b Q R \<and> bet C Q A` by blast
	have "col C D B" using col_b `axioms` `bet C D B \<and> seg_eq D B C D` by blast
	have "col B C D" using collinearorder[OF `axioms` `col C D B`] by blast
	have "parallel c b D C" using collinearparallel[OF `axioms` `parallel c b B C` `col B C D` `D \<noteq> C`] .
	have "parallel D C c b" using parallelsymmetric[OF `axioms` `parallel c b D C`] .
	have "col c A b" using col_b `axioms` `bet c A b \<and> ang_eq b A D A D B \<and> ang_eq b A D B D A \<and> ang_eq D A b B D A \<and> ang_eq c A D A D C \<and> ang_eq c A D C D A \<and> ang_eq D A c C D A \<and> parallel c b B C \<and> seg_eq c A D C \<and> seg_eq A b B D \<and> seg_eq A M M D \<and> seg_eq c M M C \<and> seg_eq B M M b \<and> bet c M C \<and> bet B M b \<and> bet A M D` by blast
	have "col c b A" using collinearorder[OF `axioms` `col c A b`] by blast
	have "A \<noteq> b" using betweennotequal[OF `axioms` `bet c A b`] by blast
	have "parallel D C A b" using collinearparallel[OF `axioms` `parallel D C c b` `col c b A` `A \<noteq> b`] .
	have "parallel A b D C" using parallelsymmetric[OF `axioms` `parallel D C A b`] .
	have "parallel b A C D" using parallelflip[OF `axioms` `parallel A b D C`] by blast
	have "seg_eq A b B D" using `bet c A b \<and> ang_eq b A D A D B \<and> ang_eq b A D B D A \<and> ang_eq D A b B D A \<and> ang_eq c A D A D C \<and> ang_eq c A D C D A \<and> ang_eq D A c C D A \<and> parallel c b B C \<and> seg_eq c A D C \<and> seg_eq A b B D \<and> seg_eq A M M D \<and> seg_eq c M M C \<and> seg_eq B M M b \<and> bet c M C \<and> bet B M b \<and> bet A M D` by blast
	have "seg_eq D B C D" using `bet C D B \<and> seg_eq D B C D` by blast
	have "seg_eq B D D B" using equalityreverseE[OF `axioms`] .
	have "seg_eq A b D B" using congruencetransitive[OF `axioms` `seg_eq A b B D` `seg_eq B D D B`] .
	have "seg_eq A b C D" using congruencetransitive[OF `axioms` `seg_eq A b D B` `seg_eq D B C D`] .
	have "seg_eq b A C D" using congruenceflip[OF `axioms` `seg_eq A b C D`] by blast
	have "bet b Q D" using `bet b Q D` .
	have "bet A Q C" using betweennesssymmetryE[OF `axioms` `bet C Q A`] .
	have "parallel b C A D \<and> seg_eq b C A D" using Prop33[OF `axioms` `parallel b A C D` `seg_eq b A C D` `bet b Q D` `bet A Q C`] .
	have "parallel b C A D" using `parallel b C A D \<and> seg_eq b C A D` by blast
	have "parallel A b C D" using parallelflip[OF `axioms` `parallel A b D C`] by blast
	have "parallel A D b C" using parallelsymmetric[OF `axioms` `parallel b C A D`] .
	have "parallelogram A b C D" sorry
	have "parallel D C A b" using `parallel D C A b` .
	have "parallel D C E F" using `parallel D C E F` .
	have "col E F A" using `col E F A` .
	have "E = E" using equalityreflexiveE[OF `axioms`] .
	have "col E F E" using col_b `axioms` `E = E` by blast
	consider "A = F"|"A \<noteq> F" by blast
	hence col E F b
	proof (cases)
		case 1
		have "parallel D C E F" using `parallel D C E F` .
		have "F \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> F`] .
		have "A \<noteq> E" sorry
		have "parallel D C A E" using collinearparallel2[OF `axioms` `parallel D C E F` `col E F A` `col E F E` `A \<noteq> E`] .
		have "col A b E" using Playfair[OF `axioms` `parallel D C A b` `parallel D C A E`] .
		have "col F b E" sorry
		have "col E F b" using collinearorder[OF `axioms` `col F b E`] by blast
	next
		case 2
		have "parallel D C A F" using collinearparallel[OF `axioms` `parallel D C E F` `col E F A` `A \<noteq> F`] .
		have "col A b F" using Playfair[OF `axioms` `parallel D C A b` `parallel D C A F`] .
		have "col A F b" using collinearorder[OF `axioms` `col A b F`] by blast
		have "col A F E" using collinearorder[OF `axioms` `col E F A`] by blast
		have "col F b E" using collinear4[OF `axioms` `col A F b` `col A F E` `A \<noteq> F`] .
		have "col E F b" using collinearorder[OF `axioms` `col F b E`] by blast
	next
	have "parallelogram A b C D \<and> col E F b" using `parallelogram A b C D` `col E F b` by blast
	thus ?thesis by blast
qed

end