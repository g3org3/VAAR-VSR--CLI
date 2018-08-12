const fs = require('fs')
const exPath = process.env.EXPATH || './experiments'

const readDir = name => new Promise((resolve, reject) =>
  fs.readdir(name, (err, files) =>
    err ? reject(err) : resolve(files)
  )
)
const writeFile = (path, data) => new Promise((resolve, reject) =>
  fs.writeFile(path, data, (err) =>
    err ? reject(err) : resolve(true)
  )
)

const rawToJSON = name => new Promise((resolve, reject) =>
  fs.readFile(`${exPath}/${name}`, (err, data) => {
    if (err) return reject(err)
    else if (!data.toString().trim()) return resolve({ name })
    else return resolve({ ...JSON.parse(data.toString()), name })
  })
)

const Main = async () => {
  console.log({ exPath })
  await writeFile(`${exPath}/all.json`, "")
  const files = await readDir(exPath)
  const jsonFiles = files
    .filter(name => name.indexOf('.json') !== -1)
    .filter(name => name !== 'all.json')
  const experiments = await Promise.all(jsonFiles.map(rawToJSON))
  await writeFile(`${exPath}/all.json`, JSON.stringify(experiments))
  console.log({ status: "done" })
}

setInterval(() =>
Main()
, 3000)