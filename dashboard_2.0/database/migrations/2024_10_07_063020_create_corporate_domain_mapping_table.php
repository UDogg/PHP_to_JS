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
        Schema::create('corporate_domain_mapping', function (Blueprint $table) {
            $table->id();
            $table->string('domain_name');
            $table->string('corporate_id');
            $table->enum('status', ['Y', 'N'])->default('N'); 
            $table->enum('is_verified', ['Y', 'N'])->default('N');
            $table->timestamps();
            $table->softDeletes();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('corporate_domain_mapping');
    }
};
