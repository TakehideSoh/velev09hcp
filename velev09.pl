#!/usr/bin/perl -w
use warnings;
use Getopt::Long;
use strict;
use POSIX;
use IO::Handle;
use IPC::Open2;
use File::Basename;
use Time::HiRes;

# Path for SAT solvers
# my $SATsolver = "/Users/soh/app/minisat-master/build/release/bin/minisat";
my $SATsolver = "/Users/soh/app/cadical-sc2020-45029f8/build/cadical";

# Parser of *.col file
# require "./parser.pl";

# Path for output files
my $cnfFile = "/tmp/velev$$.cnf";
my $outFile = "/tmp/velev$$.out";

# Variables for command line options
my (
    $debug, $help, $inter, $inverse, $type, $verbose,
    $velve, $detail, $timeLimit, $tag, $keep
);
$timeLimit = 18446744073709551615;

my $time0 = time;

$tag = "default";

# Command line options
&GetOptions(
    'verbose'   => \$verbose,
    'solver=s'   => \$SATsolver,
    'debug'   => \$debug,
    'help'    => \$help,
    'inter'   => \$inter,
    'type'    => \$type,
    'detail'  => \$detail,
    'limit=s' => \$timeLimit,
    'cnf=s' => \$cnfFile,
    'out=s' => \$outFile,
    'tag=s'   => \$tag,
    'keep'    => \$keep,
);
$inverse = 1;

if (@ARGV != 1 || $help) {
    &usage();
}

my %varNum = ();
my %numVar = ();
my $inputFile = $ARGV[0];
my @suffix_list = qw/.col/;
my ($filename, $path, $suffix) = fileparse($inputFile, @suffix_list);
my $solverPID;

my @var_o = ();
my @var_s = ();
my $var_o_start;

my $nof_nodes = 0;
my $nof_edges = 0;
my @outputs = ();
my %timeDetail = ();

my $nof_cls = 0;

sub usage {
    print "Usage: $0 [options] graph_file\n";
    print "\t-h -help         : show help\n";
    print "\t-debug level     : debug option\n";
    exit(1);
}

&main();
exit 0;

sub log {
    $_ = join(" ", @_);
    if (/ERROR/i || $verbose) {
        my $time = time - $time0;
        print "c $time\t", $_, "\n";
    }
}


sub handler {
    print "sending kill\n";
    $SIG{'INT'} = 'IGNORE';
    $SIG{'TERM'} = 'IGNORE';
    kill(-2, $solverPID);
    $SIG{'INT'} = 'DEFAULT';
    $SIG{'TERM'} = 'DEFAULT';
    if ($solverPID) {
        print "$solverPID... \n";
        kill(2, $solverPID);
    }
}

######################################
# Main
######################################
sub main {
    $SIG{'INT'} = \&handler;
    $SIG{'TERM'} = \&handler;
    my ($t1, $t2, $t3, $t4, $t5);

    eval {

        # メッセージを指定 \n は必要なので注意
        local $SIG{ALRM} = sub { die "alarm\n" };

        # alarm は指定時間経過するとプログラムを終了する
        alarm $timeLimit;

        $t1 = Time::HiRes::time;

        push(@outputs, "velev");
        push(@outputs, $tag);
        push(@outputs, $filename);

        # 1. 入力 (グラフファイル) の読み込み
        &log("reading input file.");
        my $R_Ref;
        my $exists_deg1_node = 0;
        ($R_Ref, $nof_nodes, $nof_edges, $exists_deg1_node) =
            &readFile($inputFile, $type);

        #	&showGraph($R_Ref);

        if ($exists_deg1_node) {

            # print "there is clearly no hamiltonian\n";
            while (@outputs < 7) {
                push(@outputs, "N.A.");
            }
            push(@outputs, "UNSAT");
            $t2 = Time::HiRes::time;
            $timeDetail{"pre"} = sprintf("%.3f", $t2 - $t1);
            push(@outputs, ($timeDetail{"pre"}, "", "", "", ""));
            my $line = join(",", @outputs);
            print "$line\n";
            exit();
        }

        if ($exists_deg1_node) {
            print "what is happen??\n";
            exit();
        }
        push(@outputs, ($nof_nodes, $nof_edges));

        # 2. 開始ノードの選択
        &log("finding the first node.");
        my $firstNode = &findFirstNode($R_Ref, "average");

        #	print "$firstNode\n";

        # 3. Relational Graph [Velev '09] 作成
        &log("creating chordal graph.");
        my ($Rb_Ref) = &R2Rb($R_Ref, $firstNode);

        # 4. Chordal (Triangulated) Graph [Velev '09] 作成
        my ($Rt_Ref) = &Rb2Rt($Rb_Ref, "t4");

        $t2 = Time::HiRes::time;
        $timeDetail{"pre"} = sprintf("%.3f", $t2 - $t1);

        # 5. 制約出力
        &log("generating constraints.");
        &velev($R_Ref, $Rt_Ref, $firstNode);

        $t3 = Time::HiRes::time;
        $timeDetail{"saten"} = sprintf("%.3f", $t3 - $t2);

        # 6. SAT solver の実行
        &log("executing SAT solver.");
        my @solution = &execSATsolver($cnfFile);

        $t4 = Time::HiRes::time;
        $timeDetail{"solver"} = sprintf("%.3f", $t4 - $t3);

        # 7. 結果ファイルのデコード・検証
        &log("decoding/validating results.");
        &decodeSatSolverResult($firstNode, $R_Ref, \@solution);
        $t5 = Time::HiRes::time;

        $timeDetail{"decode"} = sprintf("%.3f", $t5 - $t4);
        $timeDetail{"total"} = sprintf("%.3f", $t5 - $t1);

        alarm 0;
    };

    # エラー (ALRM, その他) により終了されていると $@ == 1 と同じなので if の分岐に入る
    if ($@) {
        while (@outputs < 7) {
            push(@outputs, "N.A.");
        }
        my $preTime = 0;
        my $encodeTime = 0;
        my $solverTime = 0;

        $t5 = Time::HiRes::time;
        $timeDetail{"total"} = sprintf("%.3f", $t5 - $t1);

        if (!exists $timeDetail{"pre"}) {
            push(@outputs, "T.O.(ENCODE1)");
            $preTime = sprintf("%.3f", $t5 - $t1);
            $encodeTime = 0;
            $solverTime = 0;
        }
        elsif (!exists $timeDetail{"saten"}) {
            push(@outputs, "T.O.(ENCODE2)");
            $preTime = $timeDetail{"pre"};
            $encodeTime = sprintf("%.3f", $t5 - $t2);
            $solverTime = 0;
        }
        elsif (!exists $timeDetail{"solver"}) {
            push(@outputs, "T.O.(SOLVER)");
            $preTime = $timeDetail{"pre"};
            $encodeTime = $timeDetail{"saten"};
            $solverTime = sprintf("%.3f", $t5 - $t3);
        }
        else {
            push(@outputs, "T.O.(OTHER)");
            $preTime = $timeDetail{"pre"};
            $encodeTime = $timeDetail{"saten"};
            $solverTime = $timeDetail{"solver"};
        }

        #	push(@outputs,"N.A.");
        #	print "PID $solverPID is being killed....\n";
        if ($solverPID) {
            kill(2, $solverPID);
        }
        wait;
        die
            unless $@ eq "alarm\n"
        ; # "alarm\n" で eval を抜けてきたのでなければ die

        push(@outputs,
            ($timeDetail{"total"}, $preTime, $encodeTime, $solverTime));

        my $line = join(",", @outputs);
        # print "$line\n";
        &log("$line");
        print "Interrupted\n";

        if (!$keep) {
            unlink $cnfFile;
            unlink $outFile;
        }

        # 正常終了だと $@ == 0 と同じなので else の分岐に入る
    }
    else {
        wait;
        my $preTime = (exists $timeDetail{"pre"}) ? $timeDetail{"pre"} : -1;
        my $encodeTime =
            (exists $timeDetail{"saten"}) ? $timeDetail{"saten"} : -1;
        my $solverTime =
            (exists $timeDetail{"saten"}) ? $timeDetail{"solver"} : -1;
        push(@outputs,
            ($timeDetail{"total"}, $preTime, $encodeTime, $solverTime));
        my $line = join(",", @outputs);
        # print "$line\n";
        &log("$line");


        if (!$keep) {
            unlink $cnfFile;
            unlink $outFile;
        }

    }

}

sub velev {
    my ($R_Ref, $Rt_Ref, $firstNode) = @_;

    # 制約の出力（中間)
    my @Clss = ();
    my $Clss_Ref = \@Clss;
    my @t;

    &defineVar($R_Ref, $Rt_Ref);

    my $num_of_vars = keys %varNum;

    open(CNF, ">$cnfFile") || die;
    my $tmp = "p cnf";
    print CNF substr($tmp . " " x 63, 0, 63) . "\n";

    $t[0] = Time::HiRes::time;
    $Clss_Ref = &varS_least_most_one($R_Ref, $firstNode, $Clss_Ref);
    $t[1] = Time::HiRes::time;
    $Clss_Ref = &Transitivity($Rt_Ref, $firstNode, $Clss_Ref);
    $t[2] = Time::HiRes::time;
    $Clss_Ref = &relFirstNode($R_Ref, $firstNode, $Clss_Ref);
    $t[3] = Time::HiRes::time;
    $Clss_Ref = &relLastNode($R_Ref, $firstNode, $Clss_Ref);
    $t[4] = Time::HiRes::time;
    $Clss_Ref = &varS_varO($R_Ref, $firstNode, $Clss_Ref);
    $t[5] = Time::HiRes::time;

    if ($inverse) {
        $Clss_Ref = &makeInverseTrans($R_Ref, $Rt_Ref, $firstNode, $Clss_Ref);
    }
    $t[6] = Time::HiRes::time;

    # CNF の出力
    #    &outCnfFile($Clss_Ref,$inter);
    $t[7] = Time::HiRes::time;

    close CNF;

    push(@outputs, ($num_of_vars, $nof_cls));
    open(CNF, "+<", $cnfFile) || die;
    $_ = "p cnf $num_of_vars $nof_cls";
    print CNF substr($_ . " " x 63, 0, 63) . "\n";
    close CNF;

    $timeDetail{"least_most_one"} = $t[1] - $t[0];
    $timeDetail{"transitiviry"} = $t[2] - $t[1];
    $timeDetail{"relFirstNode"} = $t[3] - $t[2];
    $timeDetail{"relLastNode"} = $t[4] - $t[3];
    $timeDetail{"varS_varO"} = $t[5] - $t[4];
    $timeDetail{"makeInverseTrans"} = $t[6] - $t[5];
    $timeDetail{"outCnfFile"} = $t[7] - $t[6];
    $timeDetail{"encode"} = $t[7] - $t[0];

    #   @{$Clss_Ref} = ();

}

sub decodeSatSolverResult {
    my ($firstNode, $R_Ref, $sol_ref) = @_;

    if (-e $outFile) {
        &decodeResultFile($firstNode, $R_Ref);
    }
    else {
        &log("read solution line");
        my $ss = &decodeAssignmentArray($R_Ref, $sol_ref);
        &validateSolution($firstNode, $ss);
    }

}

sub decodeAssignmentArray {

    my ($R_Ref, $array_ref) = @_;

    my @lits = @{ $array_ref };
    my @ss = ();
    my %ss = ();

    foreach my $i (@lits) {
        if ((0 < $i) && ($i < $var_o_start)) {
            my $n1;
            my $n2;
            if ($numVar{$i} =~ /\w\((\d+?)\,(\d+?)\)$/) {}
            $n1 = $1;
            $n2 = $2;
            if (!exists ${ ${ $R_Ref }[$n1] }{$n2}) {
                push(@outputs, "ERROR");
                exit();
            }
            else {
            }
            $ss{$n1} = $n2;
            $ss[ $n1 - 1 ]++;
        }
    }

    return \%ss;

}

sub validateSolution {

    my ($firstNode, $ss) = @_;

    my $i = $firstNode;
    &log("firstNode: $firstNode");

    print "s SATISFIABLE\n";
    my $str = "solution: ";

    my $cnt = 0;
    while ((keys %{ $ss }) > 1) {
        $str .= "$i -> ";
        $i = $ss->{$i};
        $cnt += 1;
        if ($i == $firstNode) {
            $str .= "$i";
            last;
        }
    }
    print "$str\n";

    &log("#Nodes: $nof_nodes, Length of cycle: $cnt");

    if ($nof_nodes == $cnt) {
        &log("Valid");
        push(@outputs, "VALID");
    } else {
        &log("Invalid");
        push(@outputs, "INVALID");
    }


}

sub decodeResultFile {

    my ($firstNode, $R_Ref) = @_;

    my $flag = 0;

    open(RES, "<$outFile") || die "$0: $! $outFile";
    my @lines = <RES>;
    close(RES);

    my $SatOrUnsat = shift(@lines);

    if ($SatOrUnsat eq "UNSAT") {
        push(@outputs, "UNSAT");
        $flag = 1;
    }
    elsif ($SatOrUnsat eq "SAT") {
        push(@outputs, "SAT");
    }

    my $out = shift(@lines);
    my @lits = split(/ /, $out);

    my ($ss) = &decodeAssignmentArray($R_Ref, \@lits);

    # my $nodes = @{ $R_Ref } - 1;
    #   print "#node: $nodes\n";

    if ($flag == 0) {
        &validateSolution($firstNode, $ss);
    }

}

sub execSATsolver {
    my ($file) = @_;

    my $cmd = "$SATsolver $file $outFile";

    if ($SATsolver =~ /.*minisat/) {
        $cmd = "$SATsolver $file $outFile";
    }
    else {
        $cmd = "$SATsolver $file";
    }

    &log("CMD: ", $cmd);

    #    print "$cmd\n";
    $solverPID = open(CMD, "$cmd 2>&1 |") || die;
    my $assignment = "";
    while (<CMD>) {
        chomp;
        &log($_);
        if (/^v (.*)$/) {
            $assignment .= "$1 ";
        }
    }
    my @assignmentArray = split(/\s+/, $assignment);

    return @assignmentArray;
}

sub defineVar {
    my ($G_Ref, $Gt_Ref) = @_;
    my $c = 1;
    my $nof_G_Ref = @{ $G_Ref };

    for (my $i = 1; $i <= $nof_nodes; $i++) {
        for (my $j = $i + 1; $j <= $nof_nodes; $j++) {
            if (!exists ${ ${ $G_Ref }[$i] }{$j}) { next; }
            $varNum{"s($i,$j)"} = $c;
            $numVar{$c} = "s($i,$j)";
            $var_s[$i][$j] = $c;
            $c++;
            $varNum{"s($j,$i)"} = $c;
            $numVar{$c} = "s($j,$i)";
            $var_s[$j][$i] = $c;
            $c++;

            #	    print "s($i,$j), s($j,$i)\n";
        }
    }
    $var_o_start = $c;
    for (my $i = 1; $i < @{ $Gt_Ref }; $i++) {
        for (my $j = $i + 1; $j < @{ $Gt_Ref }; $j++) {
            if (!exists ${ ${ $Gt_Ref }[$i] }{$j}) { next; }
            $varNum{"o($i,$j)"} = $c;
            $numVar{$c} = "o($i,$j)";
            $var_o[$i][$j] = $c;
            $c++;

            #	    print "o($i,$j)\n";
        }
    }
}

sub varS_least_most_one {
    my ($G_Ref, $firstNode, $Clss_Ref) = @_;
    my @Clss = @{ $Clss_Ref };

    for (my $i = 1; $i < @{ $G_Ref }; $i++) {
        my @n = keys %{ ${ $G_Ref }[$i] };
        my @lits_succ = ();
        my @lits_prec = ();

        if ((keys %{ ${ $G_Ref }[$i] }) < 2) {
            next;
        }

        for (my $j = 0; $j < @n; $j++) {
            push(@lits_succ, $var_s[$i][ $n[$j] ]);
            push(@lits_prec, $var_s[ $n[$j] ][$i]);

            for (my $k = $j + 1; $k < @n; $k++) {
                my @lits_succ_one = ();
                my @lits_prec_one = ();

                #		print "debug -- i:$i, j:$j, k:$k, n[$j]:$n[$j], n[$k]:$n[$k]\n";
                #		push(@lits_succ_one,-1*$var_s[$i][$n[$j]]);
                #		push(@lits_succ_one,-1*$var_s[$i][$n[$k]]);

                my $line1 = "-$var_s[$i][$n[$j]]" . " -$var_s[$i][$n[$k]]";
                print CNF "$line1 0\n";
                $nof_cls++;

                #		push(@Clss,"$line1 0\n");

                #		push(@lits_prec_one,-1*$var_s[$n[$j]][$i]);
                #		push(@lits_prec_one,-1*$var_s[$n[$k]][$i]);
                my $line2 = "-$var_s[$n[$j]][$i]" . " -$var_s[$n[$k]][$i]";
                push(@Clss, "$line2 0\n");
                print CNF "$line2 0\n";
                $nof_cls++;
            }
        }
        my $line1 = join(" ", @lits_succ) . " 0\n";

        #	push(@Clss,$line1);
        print CNF $line1;
        $nof_cls++;
        my $line2 = join(" ", @lits_prec) . " 0\n";

        #	push(@Clss,$line2);
        print CNF $line1;
        $nof_cls++;
    }

    #    exit();
    return \@Clss;

}

sub Transitivity {
    my ($Gt_Ref, $firstNode, $Clss_Ref) = @_;
    my $cnt = 0;
    for (my $i = 1; $i < @{ $Gt_Ref }; $i++) {
        for (my $j = $i + 1; $j < @{ $Gt_Ref }; $j++) {
            if (exists ${ ${ $Gt_Ref }[$i] }{$j}) {
                for (my $k = $j + 1; $k < @{ $Gt_Ref }; $k++) {
                    if ((exists ${ ${ $Gt_Ref }[$j] }{$k})
                        && (exists ${ ${ $Gt_Ref }[$i] }{$k})) {
                        my @lits_trans1 = ();
                        my @lits_trans2 = ();

                        push(@lits_trans1, -1 * $var_o[$i][$j])
                        ; #"-o($i,$j)");
                        push(@lits_trans1, -1 * $var_o[$j][$k])
                        ;                                   #"-o($j,$k)");
                        push(@lits_trans1, $var_o[$i][$k]); #"o($i,$k)");

                        push(@lits_trans2, $var_o[$i][$j]); #"o($i,$j)");
                        push(@lits_trans2, $var_o[$j][$k]); #"o($j,$k)");
                        push(@lits_trans2, -1 * $var_o[$i][$k])
                        ; #"-o($i,$k)");

                        my $line1 = join(" ", @lits_trans1);
                        $line1 .= " 0 \n";

                        #			push(@{$Clss_Ref},$line1);
                        print CNF $line1;
                        $nof_cls++;
                        my $line2 = join(" ", @lits_trans2);
                        $line2 .= " 0 \n";
                        print CNF $line2;
                        $nof_cls++;

                        #			push(@{$Clss_Ref},$line2);
                    }
                }
            }
        }
    }
    return $Clss_Ref;
}

sub relFirstNode {
    my ($G_Ref, $firstNode, $Clss_Ref) = @_;
    for (my $i = 1; $i < @{ $G_Ref }; $i++) {
        if ($i == $firstNode) { next; }

        # 1stノードは全ての i ノードに先行することを書きたい
        if ($i < $firstNode) {
            my @lits_first1 = ();
            push(@lits_first1, -1 * $var_o[$i][$firstNode])
            ; #"-o($i,$firstNode)");
            my $line1 = join(" ", @lits_first1);
            $line1 .= " 0 \n";
            print CNF $line1;
            $nof_cls++;

            #	    push(@{$Clss_Ref},$line1);
            #	    push (@{$Clss_Ref},\@lits_first1);
        }
        if ($i > $firstNode) {
            my @lits_first2 = ();
            push(@lits_first2, $var_o[$firstNode][$i]); #"o($firstNode,$i)");
            my $line2 = join(" ", @lits_first2);
            $line2 .= " 0 \n";
            print CNF $line2;
            $nof_cls++;

            #	    push(@{$Clss_Ref},$line2);
            #	    push (@{$Clss_Ref},\@lits_first2);
        }
    }
    return $Clss_Ref;
}

sub relLastNode {
    my ($G_Ref, $firstNode, $Clss_Ref) = @_;
    my %last_candidates =
        %{ ${ $G_Ref }[$firstNode]
            }; # 1stノードの隣がlastノードの候補になる

    foreach my $i (keys %last_candidates) {
        for (my $j = 1; $j < @{ $G_Ref }; $j++) {
            if ($i == $j) { next; }
            my @lits_last1 = ();
            push(@lits_last1, -1 * $var_s[$i][$firstNode])
            ; #"-s($i,$firstNode)");
            # last (i) ノードは全ての j ノードに後行することを書きたい
            if ($i < $j) {
                push(@lits_last1, -1 * $var_o[$i][$j]); #"-o($i,$j)");
            }
            elsif ($j < $i) {
                push(@lits_last1, $var_o[$j][$i]); #"o($j,$i)");
            }
            my $line1 = join(" ", @lits_last1);
            $line1 .= " 0 \n";
            print CNF $line1;
            $nof_cls++;

            #	    push(@{$Clss_Ref},$line1);
            #	    push(@{$Clss_Ref},\@lits_last1);
        }
    }
    return $Clss_Ref;
}

sub varS_varO {
    my ($G_Ref, $firstNode, $Clss_Ref) = @_;

    for (my $i = 1; $i < @{ $G_Ref }; $i++) {
        for (my $j = 1; $j < @{ $G_Ref }; $j++) {
            if ($i == $j) { next; }
            if ($j == $firstNode) { next; }
            if (!exists ${ ${ $G_Ref }[$i] }{$j}) { next; }
            my @lits = ();
            push(@lits, -1 * $var_s[$i][$j]); #"-s($i,$j)");
            if ($i < $j) {
                push(@lits, $var_o[$i][$j]); #"o($i,$j)");
            }
            if ($j < $i) {
                push(@lits, -1 * $var_o[$j][$i]); #"-o($j,$i)");
            }
            my $line1 = join(" ", @lits);
            $line1 .= " 0 \n";
            print CNF $line1;
            $nof_cls++;

            #	    push(@{$Clss_Ref},$line1);
            #	    push(@{$Clss_Ref},\@lits);
        }
    }
    return $Clss_Ref;
}

sub makeInverseTrans {
    my ($G_Ref, $Gt_Ref, $firstNode, $Clss_Ref) = @_;

    my $n1 = @{ $G_Ref };
    my $n2 = @{ $Gt_Ref };

    #    print "G:$n1, Gt:$n2\n";
    #    my $n3 = @{$Clss_Ref};
    for (my $i = 1; $i < @{ $G_Ref }; $i++) {
        for (my $j = $i + 1; $j < @{ $G_Ref }; $j++) {
            if (exists ${ ${ $G_Ref }[$i] }{$j}) { #オリジナルにノードがあるなら
                for (my $k = 1; $k < @{ $Gt_Ref }; $k++) {
                    if ((exists ${ ${ $Gt_Ref }[$i] }{$k})
                        && (exists ${ ${ $Gt_Ref }[$j] }{$k})) {
                        my @lits_f = ();
                        push(@lits_f, -1 * $var_s[$i][$j]);
                        if ($i < $k) {
                            push(@lits_f, -1 * $var_o[$i][$k]);
                        } #"-o($i,$k)");} # i k
                        elsif ($k < $i) {
                            push(@lits_f, $var_o[$k][$i]);
                        } #"o($k,$i)");}
                        if ($j < $k) {
                            push(@lits_f, $var_o[$j][$k]);
                        } #"o($j,$k)");} # j k
                        elsif ($k < $j) {
                            push(@lits_f, -1 * $var_o[$k][$j]);
                        } #"-o($k,$j)");}
                        my $line1 = join(" ", @lits_f);
                        $line1 .= " 0 \n";
                        print CNF $line1;
                        $nof_cls++;

                        #			push(@{$Clss_Ref},$line1);
                        #			push(@{$Clss_Ref},\@lits_f);

                        my @lits_fi = ();
                        push(@lits_fi, -1 * $var_s[$j][$i]); #"-s($j,$i)");
                        if ($j < $k) {
                            push(@lits_fi, -1 * $var_o[$j][$k]);
                        } #"-o($j,$k)");} # j k
                        elsif ($k < $j) {
                            push(@lits_fi, $var_o[$k][$j]);
                        } #"o($k,$j)");}
                        if ($i < $k) {
                            push(@lits_fi, $var_o[$i][$k]);
                        } #"o($i,$k)");} # i k
                        elsif ($k < $i) {
                            push(@lits_fi, -1 * $var_o[$k][$i]);
                        } #"-o($k,$i)");}
                        my $line2 = join(" ", @lits_fi);
                        $line2 .= " 0 \n";
                        print CNF $line2;
                        $nof_cls++;

                        #			push(@{$Clss_Ref},$line2);
                        #			push(@{$Clss_Ref},\@lits_fi);

                        my @lits_b = ();
                        push(@lits_b, -1 * $var_s[$i][$j]); #"-s($i,$j)");
                        if ($k < $j) {
                            push(@lits_b, -1 * $var_o[$k][$j]);
                        } #"-o($k,$j)");} # k j
                        elsif ($j < $k) {
                            push(@lits_b, $var_o[$j][$k]);
                        } #"o($j,$k)");}
                        if ($k < $i) {
                            push(@lits_b, $var_o[$k][$i]);
                        } #"o($k,$i)");} # k i
                        elsif ($i < $k) {
                            push(@lits_b, -1 * $var_o[$i][$k]);
                        } #"-o($i,$k)");}
                        my $line3 = join(" ", @lits_b);
                        $line3 .= " 0 \n";
                        print CNF $line3;
                        $nof_cls++;

                        #			push(@{$Clss_Ref},$line3);
                        #			push(@{$Clss_Ref},\@lits_b);

                        my @lits_bi = ();
                        push(@lits_bi, -1 * $var_s[$j][$i]); #"-s($j,$i)");
                        if ($k < $i) {
                            push(@lits_bi, -1 * $var_o[$k][$i]);
                        } #"-o($k,$i)");} # k i
                        elsif ($i < $k) {
                            push(@lits_bi, $var_o[$i][$k]);
                        } #"o($i,$k)");}
                        if ($k < $j) {
                            push(@lits_bi, $var_o[$k][$j]);
                        } #"o($k,$j)");} # k j
                        elsif ($j < $k) {
                            push(@lits_bi, -1 * $var_o[$j][$k]);
                        } #"-o($j,$k)");}
                        my $line4 = join(" ", @lits_bi);
                        $line4 .= " 0 \n";
                        print CNF $line4;
                        $nof_cls++;

                        #			push(@{$Clss_Ref},$line4);
                        #			push(@{$Clss_Ref},\@lits_bi);
                    }
                }
            }
        }
    }

    #    my $n4 = @{$Clss_Ref};
    #    print "#Cls1: $n3, #Cls2: $n4\n";
    return $Clss_Ref;
}

sub outCnfFile {
    my ($Clss_Ref, $flag) = @_;
    my $num_of_cls = @{ $Clss_Ref };
    my $num_of_vars = keys %varNum;

    open(CNF, ">$cnfFile") || die;
    print CNF "p cnf $num_of_vars $num_of_cls\n";

    #    print "#Var $num_of_vars, #Cls $num_of_cls\n";
    push(@outputs, ($num_of_vars, $num_of_cls));
    foreach my $i (@{ $Clss_Ref }) {
        print CNF $i;

        #	print $i;
    }

    if ($flag) {
        foreach my $i (@{ $Clss_Ref }) {
            my @tmp = split(/\s+/, $i);
            foreach my $j (@tmp) {
                if ($j =~ /^-/) {
                    my $line = $j;
                    $line =~ s/^-//;
                    print "-$numVar{$line} ";
                }
                elsif ($j eq "0") {
                    print "0\n";
                }
                else {
                    print "$numVar{$j} ";
                }
            }
        }

    }

    close CNF;
}

sub findFirstNode {
    my ($G_Ref, $heuristic) = @_;
    my %G_deg = (); # 各ノードの次数を格納するハッシュ
    my $firstNode = 0;

    if ($detail) {
        print "Original Graph\n";
        &showGraph($G_Ref);
    }

    #------------------------------------------
    # f4. 与えられたグラフのノードの次数の平均のものを開始ノードにする
    #------------------------------------------
    if ($heuristic eq "average") {
        my $sum = 0;
        my $degree = 0;
        for (my $i = 1; $i < @{ $G_Ref }; $i++) {
            $degree = keys %{ ${ $G_Ref }[$i] };
            $G_deg{$i} = $degree;
            $sum += $degree;
        }

        $degree = 0;
        my $average = $sum / (keys %G_deg);

        my @inc = sort { $G_deg{$a} <=> $G_deg{$b} } (keys %G_deg);
        for (my $i = 0; $i < @inc; $i++) {
            # @inc の中は次数でソートされたノード番号が入っている
            if ($average == $G_deg{ $inc[$i] }) {
                $degree = $G_deg{ $inc[$i] };
                $firstNode = $inc[$i];
                last;
            }
            if ($average < $G_deg{ $inc[$i] }) {
                if (($G_deg{ $inc[$i] } - $average) ==
                    ($average - $G_deg{ $inc[ $i - 1 ] })) {
                    $degree = $G_deg{ $inc[ $i - 1 ] };
                    $firstNode = $inc[ $i - 1 ];
                    last;
                }
                if (($G_deg{ $inc[$i] } - $average) >
                    ($average - $G_deg{ $inc[ $i - 1 ] })) {
                    $degree = $G_deg{ $inc[ $i - 1 ] };
                    $firstNode = $inc[ $i - 1 ];
                    last;
                }
                if (($G_deg{ $inc[$i] } - $average) <
                    ($average - $G_deg{ $inc[ $i - 1 ] })) {
                    $degree = $G_deg{ $inc[$i] };
                    $firstNode = $inc[$i];
                    last;
                }
            }
        }

        # 条件を満たす一番小さいインデックスであることを保証する
        for (my $i = 1; $i < @{ $G_Ref }; $i++) {
            if ($G_deg{$i} == $degree) {
                $firstNode = $i;
                last;
            }
        }

        #	print "average: $average, 1st node: $firstNode, degree: #$degree\n";
        if ($detail) { print "Node $firstNode is chosen as the start node\n"; }
        return $firstNode;
    }

    #------------------------------------------
    # f. xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
    #------------------------------------------
}

sub showGraph {
    my $R_Ref = $_[0];
    my @R = @{ $R_Ref };
    foreach my $i (1 .. @R - 1) {
        # @Rは26
        my @keys = sort { $a <=> $b } keys %{ $R[$i] };
        my $line = join(" ", @keys);
        print "e $i $line\n";
    }
}

sub R2Rb {
    my ($R_Ref, $firstNode) = @_;
    my @R = @$R_Ref;
    my %neighbor = %{ $R[$firstNode] };
    my @Rb = ();

    # "first node" と "その他の node" の間にエッジを追加する
    foreach my $i (1 .. $nof_nodes) {
        if ($i != $firstNode) {
            ${ Rb [ $firstNode ] }{$i} = 1;
            ${ Rb [ $i ] }{$firstNode} = 1;

            #	    print "$firstNode,$i\n";
            #	    print "$i,$firstNode\n";
        }
    }

    # "first node の隣の node (i.e. last node の候補)" と "その他の node" の間にエッジを追加する
    foreach my $i (1 .. $nof_nodes) {
        if (exists $neighbor{$i}) {
            foreach my $j (1 .. $nof_nodes) {
                if (($i != $firstNode) && ($i != $j)) {
                    ${ $Rb[$i] }{$j} = 1;
                    ${ $Rb[$j] }{$i} = 1;
                }
            }
        }
        else {
            foreach my $j (keys %{ $R[$i] }) {
                ${ $Rb[$i] }{$j} = 1;
            }
        }
    }

    my @returns = \@Rb;

    # if ($detail) {
    # 	print "Relational Graph\n";
    # 	&showGraph($Rb_Ref);
    # }

    return @returns;
}

sub Rb2Rt {
    my ($Rb_Ref, $heuristic) = @_;
    my @Rb = @$Rb_Ref; # Rb のオリジナル．ハッシュ参照の配列．

    my @G = ();

    # 実体コピー
    foreach my $i (1 .. $nof_nodes) {
        my %tmp = %{ $Rb[$i] };
        $G[$i] = \%tmp;
    }

    my %G = ();
    foreach my $i (1 .. $nof_nodes) {
        $G{$i} = $G[$i];
    }

    my @Rt = ();
    foreach my $i (1 .. $nof_nodes) {
        my %tmp = %{ $Rb[$i] };
        $Rt[$i] = \%tmp;
    }

    while (0 < (keys %G)) {
        # %Gが空集合になるまでループ
        my $time1 = Time::HiRes::time;
        my @minDegree = &RankNodeDeg(\%G);
        if (0 == @minDegree) {

            #この条件を満たすときにグラフGは完全グラフ
            last;
        }
        my ($delNode, $fill_Ref) = &SearchFill_t4(\%G, \@minDegree);
        my %fill = %{ $fill_Ref };

        # まず delNode を削除
        #	print "Delete $delNode -- ";
        delete $G{$delNode};

        # delNode のエッジを削除
        foreach my $i (keys %G) {
            if (exists ${ $G{$i} }{$delNode}) {
                delete ${ $G{$i} }{$delNode};
            }
        }

        # fill を追加する
        foreach my $i (keys %fill) {
            foreach my $j (keys %{ $fill{$i} }) {

                #		print "add ($i,$j)\n";
                ${ $G{$i} }{$j} = 1;
                ${ $G{$j} }{$i} = 1;
                ${ $Rt[$i] }{$j} = 1;
                ${ $Rt[$j] }{$i} = 1;
            }
        }
    }

    # if ($detail) {
    # 	print "Chordal Graph\n";
    # 	&showGraph($Rt_Ref);
    # }

    return \@Rt;

}

sub RankNodeDeg {
    # 与えられたグラフのノードを次数で並び替える
    my ($G_Ref) = @_;
    my %G_deg = (); # 各ノードの次数を格納したハッシュ

    my @cnt = keys %{ $G_Ref };

    for (my $i = 0; $i < @cnt; $i++) {
        $G_deg{ $cnt[$i] } =
            keys %{ ${ $G_Ref }
                { $cnt[$i] } }; # 各ノードの次数を格納したハッシュ
    }

    my @tmp = &Rank(\%G_deg, "min");

    my $n1 = keys %{ ${ $G_Ref }{ $tmp[0] } };
    my $n2 = @cnt;
    if ($n1 == ($n2 - 1)) {

        # これはすなわち現在のグラフの中のノードの一番小さい次数がその(グラフのノード数-1)であることを表している．
        # すなわちこの時点でグラフは完全グラフである
        # すなわちこれ以降， 任意のノードの削除で fill は発生することがない.
        # またこれ以降の手続き繰り返しでもずっとこの条件を維持する．
        @tmp = ();
    }

    return @tmp;
}

sub Rank {
    my ($R_deg_Ref, $way) = @_;
    my @rank = keys %{ $R_deg_Ref };

    if ($way eq "min") {
        @rank = sort { ${ $R_deg_Ref }{$a} <=> ${ $R_deg_Ref }{$b} } @rank;
    }
    elsif ($way eq "max") {
        @rank = sort { ${ $R_deg_Ref }{$b} <=> ${ $R_deg_Ref }{$a} } @rank;
    }

    my @tmp = ();
    my $degree = 0;
    push(@tmp, $rank[0]);
    for (my $i = 1; $i < @rank; $i++) {
        if (${ $R_deg_Ref }{ $rank[0] } != ${ $R_deg_Ref }{ $rank[$i] }) {
            last;
        }
        push(@tmp, $rank[$i]);
    }

    @tmp = sort { $a <=> $b } @tmp;
    return @tmp;
}

sub SearchFill_t4 {
    my ($G_Ref, $minDeg_Ref) = @_;
    my %G = %{ $G_Ref };
    my @minDeg = @{ $minDeg_Ref };
    my %fillDeg = ();
    my %delNodes = ();

    foreach my $i (@minDeg) {
        my $fill = 0;
        my @neighbor = ();
        my %fillEdges = ();

        foreach my $j (keys %{ $G{$i} }) {
            push(@neighbor, $j);
        }
        @neighbor = sort { $a <=> $b } @neighbor;

        for (my $j = 0; $j < @neighbor; $j++) {
            my %tmp = ();
            for (my $k = $j + 1; $k < @neighbor; $k++) {
                if (!exists ${ $G{ $neighbor[$j] } }{ $neighbor[$k] }) {
                    $fill++;
                    $tmp{ $neighbor[$k] } = 1;
                }
            }
            if (0 < (keys %tmp)) {
                $fillEdges{ $neighbor[$j] } = \%tmp;
            }
        }
        $fillDeg{$i} = $fill;
        $delNodes{$i} = \%fillEdges;

    }

    my @maxfill = &Rank(\%fillDeg, "max");
    my $line = join(" ", @maxfill);

    return($maxfill[0], $delNodes{ $maxfill[0] });
}

sub readFile {
    my @R;
    my ($input_file,$type) = @_;
    my $nof_nodes = 0;
    my $nof_edges = 0;
    open(IN, "<$input_file") || die "$0: $! $input_file";

    if ($type) {
        while (<IN>){
            # ���Ԥ򥹥��åפ���
            if(/^\s*$/) { next; }
            # ʸ��������Ԥ�̵�뤹��
            if(/[a-z]+/) { next; }
            # �Ρ��ɿ��Τߤ򵭺ܤ��Ƥ���Ԥ�̵�뤹��
            if(/^\d+$/) { next; }

            # ���å��Ԥ�ѡ�������
            my @nodes = split;
            for (my $i=2; $i<@nodes; $i++) {
                ${$R[$nodes[0]+1]}{$nodes[$i]+1} = 1;
                my $n1 = $nodes[0]+1;
                my $n2 = $nodes[$i]+1;
                print "$n1,$n2\n";
            }
        }
    } else {
        ##�ե����뤫��ȿ�����ɤ߹���
        while (<IN>){
            # ���Ԥ򥹥��åפ���
            if(/^\s*$/){  next; }
            # �Ρ��ɿ��ȥ��å������l������
            if(/^p\s+edge[s]*\s+(\d+?)\s+(\d+?)\s*$/){
                $nof_nodes = $1;
                $nof_edges = $2;
            }
            # ���å��Ԥ�ѡ������� (�������˥��å�����Ͽ����)
            if(/^e\s+(\d+?)\s+(\d+?)\s*$/){
                my ($n1,$n2) = ($1,$2);
                if ($n1==$n2) {
                    #		    print "selfedge\n";
                    next;
                } #��ʬ���ȤؤΥ��å����Ե���
                ${$R[$n1]}{$n2} = 1;
                ${$R[$n2]}{$n1} = 1;
                next;
            }
        }
    }

    my $deg1Flag=0;
    my $noeFlag=0;
    my %old2new = (); # �Ť��ֹ椫�鿷�����ֹ�ؤμ���
    my $new_node_index=1;
    my @G=();
    my $edge_sum=0;

    for (my $i=1; $i <= $nof_nodes; $i++) {
        #�Ρ����������Ǥ�¸�ߤ����
        if ($R[$i]) {
            $old2new{$i} = $new_node_index;
            $new_node_index++;
            my $nof_neighbor = keys %{$R[$i]};
            $edge_sum += $nof_neighbor;
            if ($nof_neighbor < 2) {
                $deg1Flag=1;
            }
        } else {
            $noeFlag=1;
        }
    }

    # �Ρ����ֹ椬�ͤޤäƤ��ʤ�����դϺƹ������Ƶͤ��
    # ���κ�Ȥˤ���Υե�����ȥΡ����ֹ�ϰ��פ��ʤ��ʤ�
    if ($noeFlag) {
        #	print "reconstruct\n";
        for (my $i=1; $i <= $nof_nodes; $i++) {
            foreach my $j (keys %{$R[$i]}) {
                ${$G[$old2new{$i}]}{$old2new{$j}} = 1 ;
                ${$G[$old2new{$j}]}{$old2new{$i}} = 1 ;
                #		print "test\n";
            }
        }

        if ($edge_sum % 2) {
            print "graph reconstruction error -- abort\n";
            exit ();
        }

        $nof_nodes = $new_node_index - 1;
        $nof_edges = $edge_sum / 2;

        # for (my $i=1; $i<@G; $i++) {
        #     my $deg = keys %{$G[$i]};
        #     if ($deg < 3) {
        # 	print "deg($i)=$deg\n";
        #     }
        # }

        return (\@G, $nof_nodes, $nof_edges, $deg1Flag);
    }

    # for (my $i=1; $i<@R; $i++) {
    # 	my $deg = keys %{$R[$i]};
    # 	if ($deg < 1000) {
    # 	    print "deg($i)=$deg\n";
    # 	}
    # }

    return (\@R, $nof_nodes, $nof_edges, $deg1Flag);


}#END OF "read_file"
