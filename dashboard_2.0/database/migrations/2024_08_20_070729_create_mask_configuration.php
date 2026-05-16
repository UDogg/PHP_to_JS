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
        Schema::create('mask_configuration', function (Blueprint $table) {
            $table->id();
            $table->string('key_name');
            $table->string('masking_position');
            $table->string('masking_symbol');
            $table->enum('for_report',['0','1'])->default('0');
            $table->enum('status',['Y','N'])->default('Y');
            $table->timestamps();
            $table->softDeletes();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('table_mask_configuration');
    }
};
