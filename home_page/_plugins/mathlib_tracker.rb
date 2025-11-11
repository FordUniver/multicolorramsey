# frozen_string_literal: true

require 'yaml'

module Jekyll
  # Generator plugin to collect Mathlib contributions and create data file
  class MathlibTracker < Generator
    safe true
    priority :high

    def generate(site)
      Jekyll.logger.info 'MathlibTracker:', 'Collecting contributions...'

      # Path to ToMathlib directory relative to site root
      tomathlib_path = File.join(site.source, '..', 'ToMathlib')

      unless Dir.exist?(tomathlib_path)
        Jekyll.logger.warn 'MathlibTracker:', "ToMathlib directory not found at #{tomathlib_path}"
        return
      end

      contributions = collect_contributions(tomathlib_path)

      # Sort contributions: merged first (most recent first), then others
      status_order = { 'merged' => 0, 'open' => 1, 'draft' => 2, 'not_started' => 3 }
      contributions.sort_by! do |c|
        [
          status_order.fetch(c['status'] || 'not_started', 99),
          -(c['merged_date']&.to_s || c['pr_number']&.to_s || c['name'] || '').hash
        ]
      end

      # Calculate summary
      summary = contributions.each_with_object(Hash.new(0)) do |contrib, counts|
        counts[contrib['status'] || 'not_started'] += 1
      end

      # Create data structure
      data = {
        'generated_at' => Time.now.utc.iso8601,
        'contributions' => contributions,
        'summary' => summary
      }

      # Write to _data directory
      data_dir = File.join(site.source, '_data')
      FileUtils.mkdir_p(data_dir)
      data_file = File.join(data_dir, 'mathlib_contributions.yaml')

      File.write(data_file, YAML.dump(data))

      Jekyll.logger.info 'MathlibTracker:', "Generated #{data_file}"
      Jekyll.logger.info 'MathlibTracker:', "Total contributions: #{contributions.size}"
      summary.each do |status, count|
        Jekyll.logger.info 'MathlibTracker:', "  #{status}: #{count}"
      end
    end

    private

    def collect_contributions(tomathlib_path)
      contributions = []

      Dir.glob(File.join(tomathlib_path, '*')).each do |subdir|
        next unless File.directory?(subdir)

        metadata_file = File.join(subdir, 'metadata.yaml')
        unless File.exist?(metadata_file)
          Jekyll.logger.warn 'MathlibTracker:', "#{File.basename(subdir)} missing metadata.yaml"
          next
        end

        begin
          metadata = YAML.load_file(metadata_file)
          contributions << metadata
        rescue => e
          Jekyll.logger.error 'MathlibTracker:', "Error reading #{metadata_file}: #{e.message}"
        end
      end

      contributions
    end
  end
end
