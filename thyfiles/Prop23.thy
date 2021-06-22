theory Prop23
	imports Axioms Definitions Theorems
begin

theorem Prop23:
	assumes: `axioms`
		"A \<noteq> B"
		"\<not> col D C E"
	shows: "\<exists> F G. ray_on A B G \<and> ang_eq F A G D C E"
proof -
	have "\<not> (col E C D)"
	proof (rule ccontr)
		assume "col E C D"
		have "col D C E" using collinearorder[OF `axioms` `col E C D`] by blast
		show "False" using `col D C E` `\<not> col D C E` by blast
	qed
	hence "\<not> col E C D" by blast
	have "\<not> (col C E D)"
	proof (rule ccontr)
		assume "col C E D"
		have "col D C E" using collinearorder[OF `axioms` `col C E D`] by blast
		show "False" using `col D C E` `\<not> col D C E` by blast
	qed
	hence "\<not> col C E D" by blast
	have "triangle D C E" using triangle_b[OF `axioms` `\<not> col D C E`] .
	have "triangle C E D" using triangle_b[OF `axioms` `\<not> col C E D`] .
	have "triangle E C D" using triangle_b[OF `axioms` `\<not> col E C D`] .
	have "seg_sum_gt C D D E C E" using Prop20[OF `axioms` `triangle D C E`] .
	have "seg_sum_gt C E E D C D" using Prop20[OF `axioms` `triangle E C D`] .
	have "seg_sum_gt E C C D E D" using Prop20[OF `axioms` `triangle C E D`] .
	have "seg_sum_gt C D E C E D" using TGsymmetric[OF `axioms` `seg_sum_gt E C C D E D`] .
	have "seg_sum_gt C D D E E C" using TGflip[OF `axioms` `seg_sum_gt C D D E C E`] by blast
	have "seg_sum_gt D E C D E C" using TGsymmetric[OF `axioms` `seg_sum_gt C D D E E C`] .
	have "seg_sum_gt E D C D E C" using TGflip[OF `axioms` `seg_sum_gt D E C D E C`] by blast
	have "seg_sum_gt C D E D E C" using TGsymmetric[OF `axioms` `seg_sum_gt E D C D E C`] .
	have "seg_sum_gt E C E D C D" using TGflip[OF `axioms` `seg_sum_gt C E E D C D`] by blast
	obtain F G where "seg_eq A G E C \<and> seg_eq A F C D \<and> seg_eq G F E D \<and> ray_on A B G \<and> triangle A G F" using Prop22[OF `axioms` `seg_sum_gt C D E C E D` `seg_sum_gt C D E D E C` `seg_sum_gt E C E D C D` `A \<noteq> B`]  by  blast
	have "seg_eq A G E C" using `seg_eq A G E C \<and> seg_eq A F C D \<and> seg_eq G F E D \<and> ray_on A B G \<and> triangle A G F` by blast
	have "seg_eq A G C E" using congruenceflip[OF `axioms` `seg_eq A G E C`] by blast
	have "seg_eq A F C D" using `seg_eq A G E C \<and> seg_eq A F C D \<and> seg_eq G F E D \<and> ray_on A B G \<and> triangle A G F` by blast
	have "seg_eq G F E D" using `seg_eq A G E C \<and> seg_eq A F C D \<and> seg_eq G F E D \<and> ray_on A B G \<and> triangle A G F` by blast
	have "seg_eq F G D E" using congruenceflip[OF `axioms` `seg_eq G F E D`] by blast
	have "ray_on A B G" using `seg_eq A G E C \<and> seg_eq A F C D \<and> seg_eq G F E D \<and> ray_on A B G \<and> triangle A G F` by blast
	have "triangle A G F" using `seg_eq A G E C \<and> seg_eq A F C D \<and> seg_eq G F E D \<and> ray_on A B G \<and> triangle A G F` by blast
	have "E = E" using equalityreflexiveE[OF `axioms`] .
	have "D = D" using equalityreflexiveE[OF `axioms`] .
	have "F = F" using equalityreflexiveE[OF `axioms`] .
	have "G = G" using equalityreflexiveE[OF `axioms`] .
	have "\<not> (C = E)"
	proof (rule ccontr)
		assume "C = E"
		have "col D C E" using collinear_b `axioms` `C = E` by blast
		show "False" using `col D C E` `\<not> col D C E` by blast
	qed
	hence "C \<noteq> E" by blast
	have "\<not> (C = D)"
	proof (rule ccontr)
		assume "C = D"
		have "col C D E" using collinear_b `axioms` `C = D` by blast
		have "col D C E" using collinearorder[OF `axioms` `col C D E`] by blast
		show "False" using `col D C E` `\<not> col D C E` by blast
	qed
	hence "C \<noteq> D" by blast
	have "ray_on C E E" using ray4 `axioms` `E = E` `C \<noteq> E` by blast
	have "ray_on C D D" using ray4 `axioms` `D = D` `C \<noteq> D` by blast
	have "\<not> (col F A G)"
	proof (rule ccontr)
		assume "col F A G"
		have "col A G F" using collinearorder[OF `axioms` `col F A G`] by blast
		have "\<not> col A G F" using triangle_f[OF `axioms` `triangle A G F`] .
		show "False" using `\<not> col A G F` `col A G F` by blast
	qed
	hence "\<not> col F A G" by blast
	have "\<not> (A = F)"
	proof (rule ccontr)
		assume "A = F"
		have "col A F G" using collinear_b `axioms` `A = F` by blast
		have "col F A G" using collinearorder[OF `axioms` `col A F G`] by blast
		show "False" using `col F A G` `\<not> col F A G` by blast
	qed
	hence "A \<noteq> F" by blast
	have "ray_on A F F" using ray4 `axioms` `F = F` `A \<noteq> F` by blast
	have "\<not> (A = G)"
	proof (rule ccontr)
		assume "A = G"
		have "col A G F" using collinear_b `axioms` `A = G` by blast
		have "col F A G" using collinearorder[OF `axioms` `col A G F`] by blast
		show "False" using `col F A G` `\<not> col F A G` by blast
	qed
	hence "A \<noteq> G" by blast
	have "ray_on A G G" using ray4 `axioms` `G = G` `A \<noteq> G` by blast
	have "ang_eq F A G D C E" using equalangles_b[OF `axioms` `ray_on A F F` `ray_on A G G` `ray_on C D D` `ray_on C E E` `seg_eq A F C D` `seg_eq A G C E` `seg_eq F G D E` `\<not> col F A G`] .
	have "ray_on A B G \<and> ang_eq F A G D C E" using `seg_eq A G E C \<and> seg_eq A F C D \<and> seg_eq G F E D \<and> ray_on A B G \<and> triangle A G F` `ang_eq F A G D C E` by blast
	thus ?thesis by blast
qed

end