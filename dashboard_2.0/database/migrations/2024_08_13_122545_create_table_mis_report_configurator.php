<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        Schema::create('mis_report_configurator', function (Blueprint $table) {
            $table->id('mis_report_configurator_id');
            $table->string('lob_id');
            $table->string('role_id');
            $table->string('status_id');
            $table->string('template_name');
            $table->enum('status', ['Y', 'N'])->default('Y');
            $table->timestamps();
            $table->softDeletes();

        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('mis_report_configurator');
    }
};
