theory angletrichotomy2
	imports Axioms Definitions Theorems
begin

theorem angletrichotomy2:
	assumes: `axioms`
		"\<not> col A B C"
		"\<not> col D E F"
		"\<not> (ang_eq A B C D E F)"
		"\<not> (ang_lt D E F A B C)"
	shows: "ang_lt A B C D E F"
proof -
	have "\<not> (B = A)"
	proof (rule ccontr)
		assume "B = A"
		have "A = B" using equalitysymmetric[OF `axioms` `B = A`] .
		have "col A B C" sorry
		show "False" sorry
	qed
	hence "B \<noteq> A" by blast
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "B = C"
		have "col A B C" sorry
		show "False" sorry
	qed
	hence "B \<noteq> C" by blast
	have "\<not> (col B A C)"
	proof (rule ccontr)
		assume "col B A C"
		have "col A B C" using collinearorder[OF `axioms` `col B A C`] by blast
		show "False" sorry
	qed
	hence "\<not> col B A C" by blast
	obtain G J where "ray_on B A J \<and> ang_eq G B J D E F \<and> same_side G C B A" using Prop23C[OF `axioms` `B \<noteq> A` `\<not> col D E F` `\<not> col B A C`]  by  blast
	have "ray_on B A J" using `ray_on B A J \<and> ang_eq G B J D E F \<and> same_side G C B A` by simp
	have "ang_eq G B J D E F" using `ray_on B A J \<and> ang_eq G B J D E F \<and> same_side G C B A` by simp
	have "same_side G C B A" using `ray_on B A J \<and> ang_eq G B J D E F \<and> same_side G C B A` by simp
	have "\<not> col B A G" sorry
	have "\<not> (B = G)"
	proof (rule ccontr)
		assume "B = G"
		have "col B A G" sorry
		show "False" sorry
	qed
	hence "B \<noteq> G" by blast
	have "\<not> (A = G)"
	proof (rule ccontr)
		assume "A = G"
		have "col B A G" sorry
		show "False" sorry
	qed
	hence "A \<noteq> G" by blast
	have "ang_eq D E F G B J" using equalanglessymmetric[OF `axioms` `ang_eq G B J D E F`] .
	have "ray_on B J A" using ray5[OF `axioms` `ray_on B A J`] .
	have "G = G" sorry
	have "ray_on B G G" sorry
	have "ang_eq D E F G B A" using equalangleshelper[OF `axioms` `ang_eq D E F G B J` `ray_on B G G` `ray_on B J A`] .
	have "\<not> col G B A" using equalanglesNC[OF `axioms` `ang_eq D E F G B A`] .
	have "\<not> (col A B G)"
	proof (rule ccontr)
		assume "col A B G"
		have "col B A G" using collinearorder[OF `axioms` `col A B G`] by blast
		show "False" sorry
	qed
	hence "\<not> col A B G" by blast
	have "ang_eq G B A D E F" using equalanglessymmetric[OF `axioms` `ang_eq D E F G B A`] .
	have "ang_eq A B G G B A" using ABCequalsCBA[OF `axioms` `\<not> col A B G`] .
	have "ang_eq A B G D E F" using equalanglestransitive[OF `axioms` `ang_eq A B G G B A` `ang_eq G B A D E F`] .
	have "\<not> (col A B G)"
	proof (rule ccontr)
		assume "col A B G"
		have "col G B A" using collinearorder[OF `axioms` `col A B G`] by blast
		show "False" sorry
	qed
	hence "\<not> col A B G" by blast
	have "\<not> (G = A)"
	proof (rule ccontr)
		assume "G = A"
		have "A = G" using equalitysymmetric[OF `axioms` `G = A`] .
		have "col A B G" sorry
		show "False" sorry
	qed
	hence "G \<noteq> A" by blast
	obtain P where "bet G A P \<and> seg_eq A P G A" sorry
	have "bet G A P" using `bet G A P \<and> seg_eq A P G A` by simp
	have "A = A" sorry
	have "col B A A" sorry
	have "\<not> (col B A G)"
	proof (rule ccontr)
		assume "col B A G"
		have "col G B A" using collinearorder[OF `axioms` `col B A G`] by blast
		show "False" sorry
	qed
	hence "\<not> col B A G" by blast
	have "same_side C G B A" using samesidesymmetric[OF `axioms` `same_side G C B A`] by blast
	have "oppo_side G B A P" sorry
	have "oppo_side C B A P" using planeseparation[OF `axioms` `same_side C G B A` `oppo_side G B A P`] .
	obtain R where "bet C R P \<and> col B A R \<and> \<not> col B A C" sorry
	have "bet C R P" using `bet C R P \<and> col B A R \<and> \<not> col B A C` by simp
	have "bet P R C" using betweennesssymmetryE[OF `axioms` `bet C R P`] .
	have "\<not> col B A C" using `\<not> col B A C` .
