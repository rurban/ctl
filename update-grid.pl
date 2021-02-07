#!/usr/bin/perl
# update the grid from the sorted list in README.md and
# crosscheck with the tests if it is stable (x), not yet implemented () or still
# broken (.).

use strict;

open my $in, '<', 'README.md' or die "$! README.md";
my @c = qw(vec str arr deq list set map uset umap pqu que stk);
my %long = (
  vec => 'vector',
  str => 'string',
  arr => 'array',
  deq => 'deque',
  list => 'list',
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
  #$found = 0 if /^```/;
  $found = 0 if /^## /;
  if ($found and /^\|`(\w+)`/) {
    push @m, $1;
    push @l, $_; # for diff
    $m->{$1} = {};
  }
  if ($found and /^\|(\w+)/) { # older format
    push @m, $1;
    push @l, $_; # for diff
    $m->{$1} = {};
  }
}
close $in;

# check all tests for its status
sub status {
  my ($c,$f) = @_;
  open my $in, '<', $f or die "$! $f";
  my ($status, %seen);
  while (<$in>) {
    if (/^#define FOREACH_METH/) {
      $status = 'x';
    }
    elsif (/^#define FOREACH_DEBUG/) {
      $status = '.';
    }
    #elsif (/^#define GENERATE_ENUM/) {
    #  close $in;
    #  return;
    #}
    elsif (/^\s+TEST\((\w+)\)/) {
      next if $1 eq 'SELF';
      $m->{$c}->{lc $1} = $status;
    }
    elsif (/^\s+case TEST_(\w+):/) {
      $seen{lc $1}++;
    }
  }
  close $in;
  my @keys = keys %{$m->{$c}};
  foreach (@keys) {
    # check if the test case is defined or not
    next if $m->{$c}->{$_} eq 'x';
    if (!exists $seen{$_}) {
      $m->{$c}->{$_} = '';
    }
  }
}

for (keys %long) {
  my $f = "tests/func/test_" . $long{$_} . ".cc";
  die "no $f $!" unless -e $f;
  status($_,$f);
}

# add common methods, untested per se
for my $c (@c) {
  for (qw(init init_from free equal size max_size empty)) {
    $m->{$c}->{$_} = 'x';
  }
}
$m->{list}->{erase_node} = 'x';
$m->{set}->{erase_node} = 'x';
for my $c (qw(vec str arr deq list set map uset umap)) {
  for (qw(begin end next foreach)) {
    $m->{$c}->{$_} = 'x';
  }
}
for my $c (qw(vec str arr deq list set map)) {
  for (qw(advance distance ref range foreach_range foreach_n foreach_n_range)) {
    $m->{$c}->{$_} = 'x';
  }
}
for my $c (qw(uset umap)) {
  for (qw(load_factor max_load_factor max_bucket_count bucket_size)) {
    $m->{$c}->{$_} = 'x';
  }
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
for (@m) {
  my $L = $M - length($_);
  my $s = sprintf("|`%s`%s", $_, ' ' x $L);
  # sort methods in $m->{$c} by order in @c
  for my $c (@c) {
    my $x = $m->{$c}->{$_};
    $x = '' unless $x;
    $s .= sprintf "| %-3s", $x;
    #push @x, sprintf("| %-3s", $x);
  }
  $s .= "|\n";
  #push @x, "|\n";
  printf $s;
  push @n, $s;
  if (/^\|`(key_compare|range)\s/) {
    line();
    hdr();
    line();
  }
}
line();
hdr();

sub update {
  open my $in, '<', 'README.md' or die "$! README.md";
  open my $out, '>', 'README.md.tmp' or die "$! README.md.tmp";
  $found = 0;
  while (<$in>) {
    if (!$found and /^\|       \s+\|vec\s+\|str\s+/) {
      $found++;
    }
    #$found = 0 if /^```/;
    $found = 0 if /^## /;
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
