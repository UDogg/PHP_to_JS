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
        Schema::create('section_fields', function (Blueprint $table) {
            $table->id('field_id');
            $table->string('lob');
            $table->string('service_support_type');
            $table->string('section_name');
            $table->string('section_field_name');
            $table->timestamps();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('section_fields');
    }
};
