#!/usr/bin/perl
# update the grid from the sorted list in README.md and
# crosscheck with the tests if it is stable (x), not yet implemented () or still
# broken (.).

use strict;
use utf8;
use feature 'unicode_strings';
binmode(STDOUT, ":utf8");

open my $in, '<:utf8', 'README.md' or die "$! README.md";
my @c = qw(vec str arr deq list slst set map uset umap pqu que stk);
my %long = (
  vec => 'vector',
  str => 'string',
  arr => 'array',
  deq => 'deque',
  list => 'list',
  slst => 'forward_list',
  set => 'set',
  map => 'map',
  uset => 'unordered_set',
  umap => 'unordered_map',
  pqu => 'priority_queue',
  que => 'queue',
  stk => 'stack',
);
my $m = {};
my ($found, @m, @l, @n);
while (<$in>) {
  if (/^\|--------------------+\|/) {
    $found++; next;
  }
  next if /^\|\s+\|vec/;
  # $found = 0 if /^```/;
  $found = 0 unless /^\|/;
  # $found = 0 if /^## /;
  if ($found and /^\|`(\w+)`/) {
    my $n = $1;
    push @m, $n;
    push @l, $_; # for diff
    # status per col
    my @s = split / \| /;
    shift @s;
    my ($i, %hash);
    for (@s) {
      s/\|//g;
      s/\s*//g;
    }
    %hash = map { $_ => $s[$i++] } @c;
    if (scalar @s != scalar @c) {
      warn "$n ",scalar @s," fields, expected ", scalar @c;
    }
    $m->{$n} = \%hash;
  }
  #if ($found and /^\|(\w+)/) { # older format
  #  push @m, $1;
  #  push @l, $_; # for diff
  #  $m->{$1} = {};
  #}
}
close $in;

# check all tests for its status
sub status {
  my ($c,$f) = @_;
  open my $in, '<', $f or die "$! $f";
  my ($status, %seen);
  while (<$in>) {
    if (/^#define FOREACH_METH/) {
      $status = '✓';
    }
    elsif (/^#define FOREACH_DEBUG/) {
      $status = 'x';
    }
    #elsif (/^#define GENERATE_ENUM/) {
    #  close $in;
    #  return;
    #}
    elsif (/^\s+TEST\((\w+)\)/) {
      my $n = $1;
      my $l = lc $n;
      next if $n eq 'SELF';
      warn "overwrite undefined $c.$l -" if $m->{$l}->{$c} eq '-';
      $m->{$l}->{$c} = $status;
    }
    elsif (/^\s+case TEST_(\w+):/) {
      my $l = lc $1;
      warn "seen undefined $c.$l -" if $m->{$l}->{$c} eq '-';
      $seen{$l}++;
    }
  }
  close $in;
  my @keys = keys %{$m->{$c}};
  foreach (@keys) {
    # check if the test case is defined or not
    next if $m->{$_}->{$c} eq '✓';
    next if $m->{$_}->{$c} eq '-';
    if (!exists $seen{$_}) {
      warn "No test yet for $c.$_ \n" if $m->{$_}->{$c} eq 'x';
      $m->{$_}->{$c} = '';
    }
  }
}

for (keys %long) {
  my $f = "tests/func/test_" . $long{$_} . ".cc";
  die "no $f $!" unless -e $f;
  status($_,$f);
}

# add common methods, untested per se
# @c: vec str arr deq list set map uset umap pqu que stk
for my $c (@c) {
  for (qw(init init_from free equal size max_size empty)) {
    $m->{$_}->{$c} = '✓';
  }
}
$m->{compare}->{str} = '✓';
$m->{key_compare}->{str} = '✓';
$m->{erase_node}->{list} = '✓';
$m->{erase_node}->{set} = '✓';
for my $c (qw(vec str arr deq list slst set map uset umap)) {
  for (qw(begin end next foreach ref)) {
    $m->{$_}->{$c} = '✓';
  }
  $m->{inserter}->{$c} = $m->{copy_if}->{$c};
}
for my $c (qw(vec str arr deq list slst set map)) {
  for (qw(advance distance range foreach_range foreach_n foreach_n_range)) {
    $m->{$_}->{$c} = '✓';
  }
  $m->{distance_range}->{$c} = $m->{lower_bound_range}->{$c};
  # union tests copy_range
  if ($c ne 'set' and $c ne 'map') {
    $m->{copy_range}->{$c} = $m->{union}->{$c};
  }
  if ($c ne 'list') {
    $m->{iter_swap}->{$c} = $m->{reverse}->{$c};
  } else {
    $m->{iter_swap}->{$c} = $m->{shuffle}->{$c};
  }
}
for my $c (qw(uset umap)) {
  for (qw(load_factor max_load_factor max_bucket_count bucket_count bucket_size)) {
    $m->{$_}->{$c} = '✓';
  }
  # undefined iter methods
  for (qw(advance advance_end distance distance_range range foreach_range foreach_n foreach_n_range)) {
    $m->{$_}->{$c} = '-';
  }
  #for (@m) { # and undefined range methods. but merge_range and generic_iter algos
  #  $m->{$_}->{$c} = '-' if /_range$/;
  #}
}

# layout:
#   5 space for the col
my $M = 31; # longest method name

sub line {
  # 30 + 5x @c
  # my $x = $M + 5 * @c - 3;
  # printf "+%s+\n", '-' x $x;
  # push @n, sprintf("+%s+\n", '-' x $x);
  #printf "|" . $M x '-';
  #printf '|-----' for @c;
  #printf "|\n";
  my $s = "|" . '-' x ($M + 2);
  for (@c) {
    $s .= "|----";
  }
  $s .= "|\n";
  printf $s;
  push @n, $s;
}

sub hdr {
  #printf "|%-${M}s", '';
  #printf "|%-5s", $_ for @c;
  #printf "|\n";
  #my @x;
  my $s = "|" . ' ' x ($M + 2);
  for (@c) {
    $s .= sprintf("|%-4s", $_);
  }
  $s .= "|\n";
  printf $s;
  push @n, $s;
}

# print grid
hdr();
line();
my ($countok, $countm);
for (@m) {
  my $L = $M - length($_);
  my $s = sprintf("|`%s`%s", $_, ' ' x $L);
  # sort methods in $m->{$c} by order in @c
  for my $c (@c) {
    my $x = $m->{$_}->{$c};
    $countok++ if $x eq '✓';
    $x = '' unless $x;
    $s .= sprintf "| %-3s", $x;
    #push @x, sprintf("| %-3s", $x);
  }
  $countm++ if $s =~ /✓/;
  $s .= "|\n";
  #push @x, "|\n";
  printf $s;
  push @n, $s;
  if (/^(key_compare|range|lexicographical_compare)$/) {
    line();
    hdr();
    line();
  }
}
line();
hdr();

sub update {
  open my $in, '<:utf8', 'README.md' or die "$! README.md";
  open my $out, '>:utf8', 'README.md.tmp' or die "$! README.md.tmp";
  $found = 0;
  while (<$in>) {
    if (/We have \d+ methods/) {
      s{We have (\d+) methods in (\d+) stable variants}
       {We have $countm methods in $countok stable variants};
    }
    if (!$found and /^\|       \s+\|vec\s+\|str\s+/) {
      $found++;
    }
    $found = 0 unless /^\|/;
    # $found = 0 if /^## /;
    if ($found) {
      for (@n) {
        s/ +$//;
        print $out $_ ;
      }
      @n = ();
    } else {
      print $out $_;
    }
  }
  close $in;
  close $out;
  system("mv README.md.tmp README.md");
  system("./update-index.pl");
}

if (eval "require Algorithm::Diff;") {
  my $diff = Algorithm::Diff::diff(\@l, \@n);
  update() if $diff;
}
