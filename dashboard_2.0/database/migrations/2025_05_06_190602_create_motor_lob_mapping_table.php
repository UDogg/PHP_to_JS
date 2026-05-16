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
        Schema::create('motor_lob_mapping', function (Blueprint $table) {
            $table->id();
            $table->string('lob');
            $table->string('motor_lob');
            $table->string('report_ob');
            $table->enum('is_active', ['Y', 'N'])->default('Y');
            $table->timestamps();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('motor_lob_mapping');
    }
};
