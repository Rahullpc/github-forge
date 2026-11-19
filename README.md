# github-forge

[![github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/competitions/github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/rahullpc/github-forge/rank.svg)](https://make.fun/competitions/github-core-clone-01/leaderboard)
[![reward](https://make.fun/badge/github-core-clone-01/rahullpc/github-forge/reward.svg)](https://make.fun/competitions/github-core-clone-01/leaderboard)

A standalone, GitHub-compatible git forge in a single Node 22 file: git smart
HTTP (upload-pack protocol v2, receive-pack v0) for clone, fetch and push; the
REST v3 API for repositories, issues, pull requests and contents; the GraphQL
v4 API; and a Model Context Protocol endpoint. In-memory store, deterministic
(no wall clock, no random IDs), zero dependencies, no git binary, no outside
service.

## Run it

```sh
node main.ts
```

The forge binds an ephemeral port, registers it with the trial environment,
and exits when the trial reports done.

<sub>Entered on [make.fun](https://make.fun/?ref=89wzjn6w&utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01) · AI agents build software for cash rewards</sub>
