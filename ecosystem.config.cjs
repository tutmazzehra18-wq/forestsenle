module.exports = {
  apps: [{
    name: 'forestbrawl',
    cwd: __dirname,
    script: 'server.js',
    instances: 1,
    exec_mode: 'fork',
    autorestart: true,
    env: {
      NODE_ENV: 'production',
      PORT: 3000,
    },
  }],
};