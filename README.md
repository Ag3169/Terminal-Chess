# Terminal Chess

A feature-rich terminal-based chess game with online multiplayer, AI opponent, and advanced game analysis.

![Python](https://img.shields.io/badge/Python-3.10+-blue.svg)
![License](https://img.shields.io/badge/License-MIT-green.svg)

## Features

### 🎮 Game Modes
- **Play vs AI** - Challenge the built-in chess engine with adjustable difficulty
- **Local 2-Player** - Play against a friend on the same device
- **Online Matchmaking** - Find random opponents for rated games

### 🏆 Competitive Features
- **ELO Rating System** - Chess.com-style rating calculations
- **Leaderboards** - View top players globally
- **Rated Games** - All online matches affect your ELO

### 🔍 Game Analysis
- **Post-Game Analysis** - Analyze your online games with the engine
- **Move Classification**:
  - 📖 **BOOK** - Moves from opening theory
  - !! **BRILLIANT** - Sacrifices for significant advantage
  - ✓ **BEST** - Engine's top choice
  - ! **GOOD** - Strong move
  - **OK** - Reasonable move
  - ?! **INACCURACY** - Minor mistake
  - ? **MISTAKE** - Significant error
  - ?? **BLUNDER** - Major mistake
- **Accuracy Percentage** - See your overall performance

### 👤 Account System
- User registration and login
- Profile management
- Game history (last 3 games displayed)
- Personal statistics

### 🌐 Online Features
- TCP-based client/server architecture
- Real-time matchmaking with ELO-based pairing
- Chat during games
- Draw offers and resignations

## Installation

### Requirements
- Python 3.10 or higher
- No external dependencies required (uses standard library only)

### Setup

1. **Clone or download the repository:**
   ```bash
   cd terminalchess
   ```


## Usage

### Starting the Server

The server must be running for online features:

```bash
python3 server.py
```

The server listens on port `65433` by default.

### Starting the Client

```bash
python3 chess.py
```

## Main Menu Options

| Option | Description |
|--------|-------------|
| 1 | **Play vs AI** - Challenge the computer |
| 2 | **Local 2-Player** - Play with a friend |
| 3 | **Online Matchmaking** - Find an opponent |
| 4 | **Account Management** - Login/Register |
| 5 | **ELO Leaderboard** - View rankings |
| 6 | **Analyze a PGN line** - Analyze moves |
| 7 | **Game Analysis (Online)** - Analyze your games |
| 8 | **Configure Server** - Change server settings |
| 9 | **Toggle Offline Mode** - Enable/disable online |

## Game Controls

### During Play
- Enter moves in **SAN format** (e.g., `e4`, `Nf3`, `O-O`)
- `help` - Show help message
- `flip` - Flip the board view
- `moves` - List all legal moves
- `resign` - Resign the game
- `draw` - Offer a draw
- `chat <message>` - Send a message to opponent
- `quit` / `exit` - Leave the game

### Online Matchmaking
When in the queue:
- Auto-refreshes every 5 seconds
- Press **3** to manually check for opponents
- Matched when two players with similar ELO (±200) are found

## Account Management

### Registration
1. Select **Account Management** from main menu
2. Choose **Register New Account**
3. Enter username (3-20 characters, alphanumeric)
4. Enter password (minimum 6 characters)
5. Enter email (valid format required)

### Login
1. Select **Account Management** from main menu
2. Choose **Login**
3. Enter username and password

## Game Analysis

Access your analyzed games from the main menu:

```
7. Game Analysis (Online)
```

Features:
- View all recent games (last 20)
- Games marked with `*` are unanalyzed
- Press game number to analyze specific game
- Press `A` to analyze all unanalyzed games
- Color-coded move quality
- Accuracy percentage for each player

## Configuration

### Server Settings
- Default port: `65433`
- Default host: `localhost`
- Configure via **Option 8** in main menu

### Database
- Location: `database.json`
- Stores: users, game history, ELO ratings
- Reset with: `database_empty.json`

## File Structure

```
terminalchess/
├── chess.py              # Main client/game logic
├── server.py             # Multiplayer server
├── database.json         # User data & game history
├── database_empty.json   # Empty database template
├── README.md             # This file
├── .venv/                # Virtual environment
└── .idea/                # IDE configuration
```

## ELO System

### Calculation
- Uses standard ELO formula with K-factors
- **K=40** for new players (<30 games)
- **K=32** for standard players
- **K=24** for experienced players (2000+ ELO)
- **K=16** for masters (2400+ ELO)

### Starting Ratings
- All players start at **1200 ELO**
- Peak ELO is tracked separately

## Matchmaking

### Queue System
- Players are matched based on ELO similarity (±200 points)
- Auto-refresh every 5 seconds while waiting
- Manual refresh available (option 3)
- Colors assigned randomly

### Game Types
- All online games are **rated**
- ELO changes shown after game completion
- Games saved locally for analysis

## Troubleshooting

### "Not logged in" Error
- Ensure you're logged in via Account Management
- Check server is running
- Try reconnecting (toggle offline mode)

### Connection Issues
- Verify server is running: `python3 server.py`
- Check firewall settings for port 65433
- Use **Configure Server** to change host/port

### Game Not Saving
- Check server console for debug output
- Ensure username matches logged-in account
- Games are always saved locally even if server fails

## Technical Details

### Engine
- Alpha-beta pruning with PVS
- Iterative deepening
- Transposition tables
- Killer move heuristic
- Opening book support
- Endgame tablebases (KQK, KRK, KPK, KBNK)

### Search Depth
- Maximum depth: 128 ply
- Analysis mode: 14+ depth
- Normal play: Adaptive based on time

## License

MIT License - See LICENSE file for details

## Credits

Terminal Chess - A multiplayer chess platform
Developed with ❤️ for chess enthusiasts
